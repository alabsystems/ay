// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deferred `final_check()` driver for `ArraySolver`.
//!
//! Extracted from `lib.rs` to reduce crate root size.
//! Contains the `final_check()` method that runs expensive O(n²) array
//! axiom checks deferred from `check()` (#6282 Packet 2).

use super::*;
impl ArraySolver<'_> {
    fn filter_unapplied_final_check_lemmas(
        &self,
        mut lemmas: Vec<TheoryLemma>,
    ) -> Vec<TheoryLemma> {
        for lemma in &mut lemmas {
            lemma.clause.sort_by_key(|lit| (lit.term.0, lit.value));
            lemma.clause.dedup_by_key(|lit| (lit.term, lit.value));
        }

        let mut seen = HashSet::default();
        lemmas.retain(|lemma| seen.insert(lemma.clause.clone()));
        lemmas.retain(|lemma| !self.applied_theory_lemmas.contains(&lemma.clause));
        lemmas
    }

    /// Rebuild the ROW2-upward queue from the current array equivalence classes.
    ///
    /// The event-driven queue is drained eagerly in
    /// `check_row2_upward_with_guidance()`. Some final-check candidates only
    /// become actionable after later equalities or exact base selects appear
    /// (e.g. extensional witness terms), so final_check must repopulate these
    /// pairs before running ROW2-upward.
    fn populate_final_check_row2_upward_queue(&mut self) {
        // ROW2 upward guidance: the event-driven queue is drained eagerly in
        // `check_row2_upward_with_guidance()`. Some final-check candidates only
        // become actionable after later equalities or exact base selects appear
        // (e.g. extensional witness terms), so rebuild the queue from the
        // current array equivalence classes for completeness.
        let mut existing: HashSet<(TermId, TermId)> =
            self.pending_row2_upward.iter().copied().collect();
        let array_terms: Vec<TermId> = self.array_vars.keys().copied().collect();
        let mut checked_classes: HashSet<TermId> = HashSet::default();

        for &arr in &array_terms {
            let equiv = self.get_equiv_class(arr);
            let repr = equiv.iter().copied().min().unwrap_or(arr);
            if !checked_classes.insert(repr) {
                continue;
            }

            let mut parent_selects = Vec::new();
            let mut parent_stores = Vec::new();
            for &member in &equiv {
                let Some(data) = self.array_vars.get(&member) else {
                    continue;
                };
                parent_selects.extend(data.parent_selects.iter().copied());
                parent_stores.extend(data.parent_stores.iter().copied());
            }

            parent_selects.sort_unstable_by_key(|term| term.0);
            parent_selects.dedup();
            parent_stores.sort_unstable_by_key(|term| term.0);
            parent_stores.dedup();

            for &select in &parent_selects {
                for &store in &parent_stores {
                    if existing.insert((select, store)) {
                        self.pending_row2_upward.push((select, store));
                    }
                }
            }
        }
    }

    /// Populate event queues for final_check completeness (#6820 Step 4).
    ///
    /// Ensures that all relevant candidates are in the event queues before
    /// final_check drains them. This is needed because incremental registration
    /// may have missed candidates that arise from equality graph changes that
    /// occurred after initial registration.
    fn populate_final_check_queues(&mut self) {
        // Store chain resolution: ensure all selects on store chains are queued.
        {
            let mut existing: HashSet<TermId> = self.pending_store_chain.iter().copied().collect();
            let selects: Vec<(TermId, TermId)> = self
                .select_cache
                .iter()
                .map(|(&sel, &(arr, _))| (sel, arr))
                .collect();
            for (sel, arr) in selects {
                if existing.contains(&sel) {
                    continue;
                }
                // Queue if the select reads from a store or store-equivalent term.
                if self.store_cache.contains_key(&arr) {
                    existing.insert(sel);
                    self.pending_store_chain.push(sel);
                } else if let Some(neighbors) = self.eq_adj.get(&arr) {
                    if neighbors
                        .iter()
                        .any(|&(other, _)| self.store_cache.contains_key(&other))
                    {
                        existing.insert(sel);
                        self.pending_store_chain.push(sel);
                    }
                }
            }
        }

        // Conflicting store equalities: ensure all store pairs in the same
        // equiv class are queued.
        {
            let mut existing: HashSet<(TermId, TermId)> =
                self.pending_conflicting_stores.iter().copied().collect();
            let store_terms: Vec<TermId> = self.store_cache.keys().copied().collect();
            let mut checked_classes: HashSet<TermId> = HashSet::default();
            for &s1 in &store_terms {
                let equiv = self.get_equiv_class(s1);
                let repr = equiv.iter().copied().min().unwrap_or(s1);
                if !checked_classes.insert(repr) {
                    continue;
                }
                let stores_in_class: Vec<TermId> = equiv
                    .iter()
                    .copied()
                    .filter(|t| self.store_cache.contains_key(t))
                    .collect();
                for i in 0..stores_in_class.len() {
                    for j in (i + 1)..stores_in_class.len() {
                        let pair = (stores_in_class[i], stores_in_class[j]);
                        if existing.insert(pair) {
                            self.pending_conflicting_stores.push(pair);
                        }
                    }
                }
            }
        }

        // Array equality: ensure all true array equalities are queued.
        {
            let mut existing: HashSet<TermId> = self
                .pending_array_eqs
                .iter()
                .map(|&(eq, _, _)| eq)
                .collect();
            let eq_entries: Vec<(TermId, TermId, TermId)> = self
                .equality_cache
                .iter()
                .filter_map(|(&eq_term, &(lhs, rhs))| {
                    if self.assigns.get(&eq_term) == Some(&true)
                        && matches!(self.terms.sort(lhs), Sort::Array(_))
                        && !existing.contains(&eq_term)
                    {
                        Some((eq_term, lhs, rhs))
                    } else {
                        None
                    }
                })
                .collect();
            for (eq_term, lhs, rhs) in eq_entries {
                existing.insert(eq_term);
                self.pending_array_eqs.push((eq_term, lhs, rhs));
            }
        }
    }

    /// Deferred consistency checks that are too expensive for every `check()` call.
    ///
    /// Called by the combined theory solver when all theories report SAT and the
    /// Nelson-Oppen fixpoint has converged. Runs the O(n²) array axiom checks
    /// that were removed from `check()` for performance (#6282 Packet 2):
    ///
    /// - **ROW2 upward (axiom 2b):** `select(A, j) = select(store(A,i,v), j)` when `i ≠ j`.
    ///   Propagates selects from base arrays "up" to store results.
    /// - **ROW2 extended:** Store chain following for select pairs that normalize to
    ///   the same (base, index).
    /// - **Nested select conflicts:** Recursive simplification for 3D arrays.
    ///
    /// Reference: Z3's `theory_array::final_check_eh()` defers axiom 2b until
    /// the solver is otherwise stuck. This mirrors that pattern.
    pub fn final_check(&mut self) -> TheoryResult {
        // #8615: Early exit if the external interrupt flag is set.
        // final_check runs many expensive O(n²) sub-checks; returning Unknown
        // allows the DPLL(T) loop to detect the interrupt and abort.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        self.populate_caches();

        self.final_check_call_count += 1;

        // The pairwise-decided memo is only valid for a fixed theory state.
        // Clear it at the top of every pass so no entry outlives the equiv/diseq
        // state it was computed under (state is constant WITHIN one final_check).
        self.pairwise_decided_cache.borrow_mut().clear();
        self.store_chain_decided_cache.borrow_mut().clear();

        // #6546: Short-circuit when the equality/disequality graph and caches
        // haven't changed since the last final_check that returned Sat. The
        // O(selects^2) checks in check_row2_extended and check_nested_select_conflicts
        // dominate runtime on storeinv SAT benchmarks (e.g., 580ms/call for 152
        // selects). If no new equalities, disequalities, or terms appeared, the
        // sub-checks will return None again.
        let fc_snapshot = (
            self.eq_adj_version,
            self.diseq_set.len(),
            self.select_cache.len(),
            self.store_cache.len(),
            self.requested_model_eqs.len(),
            self.requested_interface_eqs.len(),
        );
        // Const-array vs const-array equality is decided directly and needs no
        // selects/stores, so it must be checked BEFORE the no-select/no-store
        // early-Sat short-circuit below. Without this, `(= (as const A d1)
        // (as const A d2))` with d1 != d2 (which differ at every index) is
        // wrongly admitted as Sat. (Soundness fix: const-array=const-array.)
        if let Some(conflict) = self.check_const_array_equality_conflict() {
            self.conflict_count += 1;
            return conflict;
        }

        // Const-array = store-chain over a free base: const-read obligation at every
        // effective written index (filtered to avoid re-emitting the same stable
        // lemma each round / churn).
        if let Some(TheoryResult::NeedLemmas(lemmas)) =
            self.check_const_array_store_chain_conflict()
        {
            let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
            if !lemmas.is_empty() {
                self.conflict_count += 1;
                return TheoryResult::NeedLemmas(lemmas);
            }
        }

        // A disequality between arrays whose element sort is a singleton is a
        // conflict (all such arrays are equal). Like the const-array check, this
        // needs no selects/stores, so run it before the early-Sat short-circuit.
        // (Soundness fix: card-1 element-sort array distinctness.)
        if let Some(conflict) = self.check_singleton_element_array_diseq() {
            self.conflict_count += 1;
            return conflict;
        }

        if self.final_check_snapshot == Some(fc_snapshot) {
            return TheoryResult::Sat;
        }
        if self.select_cache.is_empty() && self.store_cache.is_empty() {
            self.final_check_snapshot = Some(fc_snapshot);
            return TheoryResult::Sat;
        }

        self.build_equiv_class_cache();

        // #8615: Check interrupt after building equiv class cache.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        // #8141: Generate ALL remaining lazy ROW2 axioms (no budget) in
        // final_check to ensure completeness. If check() skipped some axioms
        // due to the budget, final_check catches them here.
        self.generate_all_lazy_row2_axioms();

        tracing::debug!(
            call = self.final_check_call_count,
            selects = self.select_cache.len(),
            stores = self.store_cache.len(),
            diseqs = self.diseq_set.len(),
            eq_adj_ver = self.eq_adj_version,
            "array final_check"
        );

        // #6820: Accumulate model equality requests across ALL sub-checks so
        // they are returned as a single batch. Previously each sub-check returned
        // early on NeedModelEquality, causing O(rounds) re-solves where each round
        // only discovered a few new pairs. Batching reduces swap size-10 from
        // 45+ rounds to ~1-3 rounds by collecting requests from both
        // check_row2_upward_with_guidance and check_disjunctive_store_target_equalities
        // in one pass. Conflicts and lemmas still return immediately.
        let mut model_eq_requests: Vec<ModelEqualityRequest> = Vec::new();

        self.populate_final_check_row2_upward_queue();

        // #8615: Check interrupt after rebuilding ROW2-upward candidates.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        // (#6282 Phase A) ROW2 upward with guidance: check for conflicts AND
        // request NeedModelEquality for undecided index pairs. The dedup set
        // (requested_model_eqs) prevents infinite N-O fixpoint restarts by
        // ensuring each undecided pair is requested at most once per problem.
        if let Some(result) = self.check_row2_upward_conflict_ready_guidance() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: ROW2-upward conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            "arrays final_check: ROW2-upward lemma batch"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!("arrays final_check: ROW2-upward NeedModelEquality (batching)");
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    tracing::debug!(
                        count = reqs.len(),
                        "arrays final_check: ROW2-upward NeedModelEqualities (batching)"
                    );
                    model_eq_requests.extend(reqs);
                }
                _ => {}
            }
        }

        // #8615: Check interrupt between sub-checks.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        // #8141: Drain any pending ROW2 down axioms generated by
        // generate_all_lazy_row2_axioms() above. These would normally be
        // drained by check_row2() in check_impl(), but final_check() runs
        // its own sub-checks. Run this after ROW2-upward guidance so repeated
        // ROW2-down lemma batches do not starve the completeness-critical
        // index-equality requests discovered from rebuilt final-check pairs.
        if let Some(result) = self.check_row2() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: ROW2-down conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            "arrays final_check: ROW2-down lemma batch"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                TheoryResult::NeedModelEquality(req) => {
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    model_eq_requests.extend(reqs);
                }
                _ => {}
            }
        }

        // #8615: Check interrupt between sub-checks.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        // ROW2 extended via store chain following.
        //
        // #k1-explain-memo: `check_row2_extended` is `&self` — the equality
        // graph, assignments, and external-fact maps are provably immutable
        // for the duration of the call (no `&mut self` alias can exist), which
        // is exactly the `eq_paths_cache` soundness precondition established
        // for `propagate_equalities_impl`. Activating the window here dedups
        // the per-candidate-pair `explain_equal/distinct_if_provable` BFS
        // recomputations that dominated final_check on axiom-expanded AUFLIA
        // re-solves (A1 chain shape: O(pairs x graph) hash-churn, >30s wall).
        if let Some(result) = {
            let _eq_paths_cache_guard = eq_paths_cache::activate();
            self.check_row2_extended()
        } {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: ROW2-extended conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            clauses = ?lemmas.iter().map(|l| &l.clause).collect::<Vec<_>>(),
                            "arrays final_check: ROW2-extended lemma batch"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                _ => {
                    tracing::debug!("arrays final_check: ROW2-extended non-sat result");
                }
            }
        }

        if !model_eq_requests.is_empty() {
            tracing::debug!(
                count = model_eq_requests.len(),
                "arrays final_check: returning exact ROW2 model equality requests"
            );
            return match model_eq_requests.len() {
                1 => TheoryResult::NeedModelEquality(
                    model_eq_requests
                        .pop()
                        .expect("invariant: len checked above"),
                ),
                _ => TheoryResult::NeedModelEqualities(model_eq_requests),
            };
        }

        // #8785: Run only the singleton part of the same-base finite-support
        // witness before exact store-permutation/nested-select checks. The
        // broad fallback can emit very large support disjunctions, while a
        // singleton support request is the precise split needed by storecomm.
        if let Some(result) = self.check_store_chain_select_difference_witness_singleton() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!(
                        "arrays final_check: store-chain-difference singleton conflict"
                    );
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            "arrays final_check: store-chain-difference singleton support lemma"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!(
                        "arrays final_check: store-chain-difference singleton NeedModelEquality"
                    );
                    self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                    return TheoryResult::NeedModelEquality(req);
                }
                TheoryResult::NeedModelEqualities(mut reqs) => {
                    tracing::debug!(
                        count = reqs.len(),
                        "arrays final_check: store-chain-difference singleton NeedModelEqualities"
                    );
                    self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                    return match reqs.len() {
                        0 => TheoryResult::Sat,
                        1 => TheoryResult::NeedModelEquality(
                            reqs.pop().expect("invariant: len checked above"),
                        ),
                        _ => TheoryResult::NeedModelEqualities(reqs),
                    };
                }
                _ => {
                    tracing::debug!("arrays final_check: store-chain-difference non-sat result");
                }
            }
        }

        // #k1-explain-memo: `&self` read-only scan — see check_row2_extended
        // note above for the memo-window soundness argument.
        if let Some(result) = {
            let _eq_paths_cache_guard = eq_paths_cache::activate();
            self.check_store_permutation_select_conflicts()
        } {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: store-permutation-select conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            "arrays final_check: store-permutation-select lemma batch"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                _ => {
                    tracing::debug!("arrays final_check: store-permutation-select non-sat result");
                }
            }
        }

        // Nested select conflicts (3D arrays via recursive simplification).
        // #k1-explain-memo: `&self` read-only scan — see check_row2_extended
        // note above for the memo-window soundness argument.
        if let Some(result) = {
            let _eq_paths_cache_guard = eq_paths_cache::activate();
            self.check_nested_select_conflicts()
        } {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: nested-select conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            "arrays final_check: nested-select lemma batch"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                _ => {
                    tracing::debug!("arrays final_check: nested-select non-sat result");
                }
            }
        }

        // #8615: Check interrupt before expensive event-driven queue population.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        // #8785: After exact store-permutation/nested-select checks have had a
        // chance to learn smaller clauses, allow the broad same-base support
        // witness as a final fallback for finite store-chain differences.
        if let Some(result) = self.check_store_chain_select_difference_witness() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: store-chain-difference conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            "arrays final_check: store-chain-difference support lemma"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!("arrays final_check: store-chain-difference NeedModelEquality");
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    tracing::debug!(
                        count = reqs.len(),
                        "arrays final_check: store-chain-difference NeedModelEqualities"
                    );
                    model_eq_requests.extend(reqs);
                }
                _ => {
                    tracing::debug!("arrays final_check: store-chain-difference non-sat result");
                }
            }
        }

        // #8615: Check interrupt before expensive event-driven queue population.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        // #6546/#6820: Store chain resolution, conflicting store equalities, and
        // array equality checks are now event-driven (Step 4). In final_check,
        // ensure completeness by populating queues with any candidates not yet
        // covered by incremental registration.
        self.populate_final_check_queues();

        if let Some(result) = self.check_store_chain_resolution() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: store-chain conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            "arrays final_check: store-chain lemma batch"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                _ => {
                    tracing::debug!("arrays final_check: store-chain non-sat result");
                }
            }
        }

        // #8615: Check interrupt between sub-checks.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        if let Some(result) = self.check_conflicting_store_equalities() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: conflicting-store-eq conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            "arrays final_check: conflicting-store-eq lemma batch"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                _ => {
                    tracing::debug!("arrays final_check: conflicting-store-eq non-sat result");
                }
            }
        }

        // #8615: Check interrupt between sub-checks.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        if let Some(result) = self.check_disjunctive_store_target_equalities() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: disjunctive-store-target conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            "arrays final_check: disjunctive-store-target lemma batch"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!(
                        "arrays final_check: disjunctive-store-target NeedModelEquality (batching)"
                    );
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    tracing::debug!(
                        count = reqs.len(),
                        "arrays final_check: disjunctive-store-target NeedModelEqualities (batching)"
                    );
                    model_eq_requests.extend(reqs);
                }
                _ => {
                    tracing::debug!("arrays final_check: disjunctive-store-target non-sat result");
                }
            }
        }

        // #8615: Check interrupt between sub-checks.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        if let Some(result) = self.check_array_equality() {
            match result {
                TheoryResult::Unsat(_) => {
                    tracing::debug!("arrays final_check: array-equality conflict");
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    let lemmas = self.filter_unapplied_final_check_lemmas(lemmas);
                    if !lemmas.is_empty() {
                        self.rollback_unreturned_model_equality_requests(&model_eq_requests);
                        tracing::debug!(
                            count = lemmas.len(),
                            "arrays final_check: array-equality lemma batch"
                        );
                        return TheoryResult::NeedLemmas(lemmas);
                    }
                }
                _ => {
                    tracing::debug!("arrays final_check: array-equality non-sat result");
                }
            }
        }

        // #8615: Check interrupt before interface equality generation.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        // Select-free store-chain-equality index split
        // (storechain_colliding_indices_sat_7654): when two same-base store
        // chains are asserted equal but no `select` term exists to drive the
        // difference witnesses above, request model equalities on the chains'
        // undecided store indices so SAT decides the collisions the equality
        // requires.
        if let Some(reqs) = self.check_store_chain_equality_index_split() {
            tracing::debug!(
                count = reqs.len(),
                "arrays final_check: store-chain-equality index split"
            );
            model_eq_requests.extend(reqs);
        }

        // #8615: Check interrupt before interface equality generation.
        if self.is_interrupted() {
            self.rollback_unreturned_model_equality_requests(&model_eq_requests);
            return TheoryResult::Unknown;
        }

        // #8531: Interface equalities for Nelson-Oppen completeness.
        // For each pair of array-sorted terms in different equivalence classes
        // and of the same sort, request a model equality so the SAT solver
        // decides whether they are equal.
        // Reference: Z3 `mk_interface_eqs` in `theory_array_base.cpp:554-582`.
        if let Some(iface_reqs) = self.check_interface_equalities() {
            model_eq_requests.extend(iface_reqs);
        }

        // #6820: Return accumulated model equality requests as one batch.
        // This reduces the number of SAT re-solve rounds for problems with
        // many undecided index pairs (swap size-10: 45 pairs).
        if !model_eq_requests.is_empty() {
            tracing::debug!(
                count = model_eq_requests.len(),
                "arrays final_check: returning batched model equality requests"
            );
            return match model_eq_requests.len() {
                1 => TheoryResult::NeedModelEquality(
                    model_eq_requests
                        .pop()
                        .expect("invariant: len checked above"),
                ),
                _ => TheoryResult::NeedModelEqualities(model_eq_requests),
            };
        }

        // All sub-checks passed — save snapshot for short-circuit (#6546).
        self.final_check_snapshot = Some(fc_snapshot);
        TheoryResult::Sat
    }

    /// Generate interface equalities for Nelson-Oppen completeness (#8531).
    ///
    /// Collects all "active" array-sorted terms (those appearing as the array
    /// argument of a select or store), groups them by sort, and for each pair
    /// of same-sort arrays in different equivalence classes (and not known
    /// disequal), requests a model equality so the SAT solver decides `a = b`.
    ///
    /// Budget: at most 10 new interface equalities per call to avoid
    /// combinatorial explosion on problems with many array variables.
    ///
    /// Reference: Z3 `theory_array_base::mk_interface_eqs` in
    /// `reference/z3/src/smt/theory_array_base.cpp:554-582`.
    pub(crate) fn check_interface_equalities(&mut self) -> Option<Vec<ModelEqualityRequest>> {
        const MAX_INTERFACE_EQS_PER_CALL: usize = 10;

        // Collect active array-sorted term roots. "Active" means the term
        // appears as the array operand of a select or store, mirroring Z3's
        // `collect_shared_vars` which collects array theory variables that
        // are shared with other theories or used as select arguments.
        let mut active_arrays: Vec<TermId> = Vec::new();
        let mut seen_roots: HashSet<TermId> = HashSet::default();

        // Arrays from select_cache: the array argument of each select.
        for &(arr, _idx) in self.select_cache.values() {
            let root = self.equiv_class_representative(arr);
            if seen_roots.insert(root) {
                active_arrays.push(root);
            }
        }

        // Arrays from store_cache: both the base array and the store result.
        for (&store_term, &(base, _idx, _val)) in &self.store_cache {
            let root_base = self.equiv_class_representative(base);
            if seen_roots.insert(root_base) {
                active_arrays.push(root_base);
            }
            let root_store = self.equiv_class_representative(store_term);
            if seen_roots.insert(root_store) {
                active_arrays.push(root_store);
            }
        }

        if active_arrays.len() < 2 {
            return None;
        }

        let mut requests = Vec::new();

        // O(n^2) pairwise comparison, budgeted.
        for (i, &a) in active_arrays.iter().enumerate() {
            if requests.len() >= MAX_INTERFACE_EQS_PER_CALL {
                break;
            }
            let sort_a = self.terms.sort(a);
            if !matches!(sort_a, Sort::Array(_)) {
                continue;
            }

            for &b in active_arrays.iter().skip(i + 1) {
                if requests.len() >= MAX_INTERFACE_EQS_PER_CALL {
                    break;
                }
                let sort_b = self.terms.sort(b);

                // Same sort check (Z3: `s1 == s2`).
                if sort_a != sort_b {
                    continue;
                }

                // Already in the same equivalence class — nothing to decide.
                if self.same_equiv_class(a, b) {
                    continue;
                }

                // Already known disequal — no need to split (Z3: `!ctx.is_diseq`).
                if self.known_distinct(a, b) {
                    continue;
                }

                // #8531: Self-store simplification guard.
                // mk_eq(store(base, i, v), base) simplifies to (= select(base, i) v)
                // via try_simplify_store_eq. If that simplified equality is already
                // decided false (or its negation is decided true), the arrays are
                // provably distinct. Without this check, the split loop repeatedly
                // encodes the simplified form while the array solver keeps requesting
                // the raw array equality that never gets created.
                if self.interface_eq_is_self_store(a, b) {
                    continue;
                }

                // #8785: Avoid speculative interface-equality splits that feed an
                // endpoint's existing store-chain alias back into SAT as a fresh
                // guessed array equality. This is intentionally endpoint-local:
                // suppress only when `a` itself unfolds to a store chain over
                // `b`'s class (or vice versa), not when some unrelated class
                // member happens to have that shape.
                if self.interface_eq_is_endpoint_store_chain_alias(a, b) {
                    continue;
                }

                // #8785: Store-commutativity benchmarks can create many
                // finite store-chain aliases over the same base array. When
                // their store indices are already equal or provably distinct,
                // ROW/store-chain reasoning has the concrete obligations; an
                // extra speculative array-interface equality only feeds large
                // alias waves back into Nelson-Oppen.
                if self.interface_eq_is_finite_same_base_store_chain_alias(a, b) {
                    continue;
                }

                // Dedup: use ordered pair of roots.
                let key = Self::ordered_pair(a, b);

                // #8594: Already-decided equality guard for non-persistent eager arm.
                // The non-persistent eager arm creates a fresh ArraySolver each
                // iteration, losing the requested_interface_eqs dedup set. When a
                // prior iteration requested (= A B) and the SAT solver encoded and
                // decided it (true or false), the fresh theory sees the equality term
                // in eq_pair_index with an assignment. Re-requesting it would waste a
                // model equality round on an already-decided split. This check makes
                // the dedup set unnecessary for equalities that were already encoded.
                if let Some(&eq_term) = self.eq_pair_index.get(&key) {
                    if self.assigns.contains_key(&eq_term) {
                        continue;
                    }
                }

                if !self.requested_interface_eqs.insert(key) {
                    continue;
                }

                tracing::debug!(
                    lhs = ?a,
                    rhs = ?b,
                    "array interface equality requested"
                );

                requests.push(ModelEqualityRequest {
                    lhs: a,
                    rhs: b,
                    reason: Vec::new(),
                    implied: false,
                });
            }
        }

        if requests.is_empty() {
            None
        } else {
            Some(requests)
        }
    }

    /// Check if `(= a b)` is a self-store pattern that mk_eq will simplify.
    ///
    /// When `a = store(base, i, v)` and `b = base` (or vice versa),
    /// `mk_eq(a, b)` simplifies to `(= select(base, i) v)` via
    /// `try_simplify_store_eq`. This means the raw array equality
    /// `(= store(base,i,v) base)` is never created in the TermStore,
    /// so the array solver can never learn it via `eq_pair_index`.
    ///
    /// The self-store axiom (`check_self_store`) already handles this
    /// case: if `store(a,i,v) = a` then `select(a,i) = v`. The interface
    /// equality is redundant — the self-store axiom will fire if the
    /// arrays are equal, and the simplified equality captures disequality.
    ///
    /// #8596: Check through equivalence classes. When `a` and `b` are
    /// representative roots, a store term may be a non-root member of
    /// `a`'s class. For example, `a = store(const(0), x, 1)` makes `a`
    /// and `store(...)` equivalent. The root is `a` (lower TermId), but
    /// the store is in its class. If `b = const(0)` (the store's base),
    /// the direct check `store_cache.get(&a)` misses the pattern because
    /// `a` itself is not a store. We must scan all members of each class
    /// for store terms whose base is in the other class.
    fn interface_eq_is_self_store(&self, a: TermId, b: TermId) -> bool {
        // Direct check (original fast path)
        if let Some(&(base, _idx, _val)) = self.store_cache.get(&a) {
            if b == base || self.same_equiv_class(b, base) {
                return true;
            }
        }
        if let Some(&(base, _idx, _val)) = self.store_cache.get(&b) {
            if a == base || self.same_equiv_class(a, base) {
                return true;
            }
        }
        // #8596: Equivalence class scan. Check if any member of `a`'s
        // equiv class is a store whose base is in `b`'s equiv class, or
        // vice versa. This catches cases like:
        //   a's class = {a, store(const(0), x, 1)}
        //   b's class = {const(0)}
        // where `a` is the root but `store(const(0), x, 1)` has base
        // `const(0)` which is in `b`'s class.
        let class_a = self.get_equiv_class(a);
        for &member in &class_a {
            if let Some(&(base, _idx, _val)) = self.store_cache.get(&member) {
                if self.same_equiv_class(b, base) {
                    return true;
                }
            }
        }
        let class_b = self.get_equiv_class(b);
        for &member in &class_b {
            if let Some(&(base, _idx, _val)) = self.store_cache.get(&member) {
                if self.same_equiv_class(a, base) {
                    return true;
                }
            }
        }
        false
    }

    fn interface_eq_is_endpoint_store_chain_alias(&self, a: TermId, b: TermId) -> bool {
        self.store_chain_reaches_equiv_class_from_endpoint(a, b)
            || self.store_chain_reaches_equiv_class_from_endpoint(b, a)
    }

    fn interface_eq_is_finite_same_base_store_chain_alias(&self, a: TermId, b: TermId) -> bool {
        let Some((base_a, indices_a)) = self.finite_store_chain_alias_summary(a) else {
            return false;
        };
        let Some((base_b, indices_b)) = self.finite_store_chain_alias_summary(b) else {
            return false;
        };

        self.same_equiv_class(base_a, base_b)
            && self.store_chain_indices_are_decided(&indices_a, &indices_b)
    }

    /// Surface undecided store-index pairs for an asserted array equality
    /// between two store chains over the same base, so the SAT solver splits on
    /// them (storechain_colliding_indices_sat_7654).
    ///
    /// SELECT-FREE completeness gap: an assertion like
    /// `store(store(a,i,v),j,x) = store(store(a,i,w),j,x)` with `v != w` is SAT
    /// only when `i = j` (the outer store shadows the inner one on both sides).
    /// Every store-chain-difference / read-over-write witness above is driven by
    /// pre-existing `select` terms (`select_alias_diseq_candidate_pairs`), but
    /// this formula has NONE, so nothing decides `i` vs `j`. Arithmetic is then
    /// free to pick `i = 0, j = 1`, and AY shipped a non-colliding model that
    /// reads `v` on one side and `w` on the other — a witness z3's pin-check
    /// rejects. The sound value-conflict detector
    /// (`check_store_chain_equality_value_conflict`) can refute the `i != j`
    /// branch but never CREATE the split.
    ///
    /// This driver creates it: for each asserted array equality between two
    /// SAME-BASE finite store chains whose store indices are not yet pairwise
    /// decided, it requests a model equality `(= idx_a idx_b)` for each undecided
    /// pair. The `i = j` branch yields the collision model; the `i != j` branch
    /// is refuted by the value-conflict detector, so SAT backtracks into the
    /// sound collision assignment. Sound by construction: a model equality is a
    /// pure SAT case split (both polarities explored), never a committed fact.
    ///
    /// Scoped to same-base chains (the exact shape whose equality forces index
    /// collisions) and bounded (`STORE_EQ_INDEX_BOUND` indices/equality) so the
    /// store-heavy unsat families stay off the split loop.
    fn check_store_chain_equality_index_split(&mut self) -> Option<Vec<ModelEqualityRequest>> {
        const STORE_EQ_INDEX_BOUND: usize = 16;

        let candidates: Vec<(TermId, TermId, TermId)> = self.pending_array_eqs.clone();
        let mut requests = Vec::new();
        let mut seen: HashSet<(TermId, TermId)> = HashSet::default();

        for (eq_term, lhs, rhs) in candidates {
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }
            if lhs == rhs {
                continue;
            }
            let Some((base_l, idxs_l)) = self.finite_store_chain_alias_summary(lhs) else {
                continue;
            };
            let Some((base_r, idxs_r)) = self.finite_store_chain_alias_summary(rhs) else {
                continue;
            };
            // Same base: the equality then forces the two chains' effective
            // writes to reconcile, which is precisely what collides indices.
            if base_l != base_r && !self.same_equiv_class(base_l, base_r) {
                continue;
            }
            let mut universe: Vec<TermId> = idxs_l;
            universe.extend(idxs_r);
            universe.sort_unstable_by_key(|t| t.0);
            universe.dedup();
            if universe.len() > STORE_EQ_INDEX_BOUND {
                continue;
            }
            // Only split when the indices are NOT already pairwise decided;
            // a fully decided chain is handled by the value-conflict detector.
            if self.store_chain_indices_are_decided(&universe, &[]) {
                continue;
            }
            for a in 0..universe.len() {
                for b in (a + 1)..universe.len() {
                    let (idx1, idx2) = (universe[a], universe[b]);
                    if self.terms.sort(idx1) != self.terms.sort(idx2) {
                        continue;
                    }
                    // Same decided-pair predicate as `store_chain_indices_are_decided`;
                    // reuse the (already-warm) memo instead of recomputing.
                    if self.pair_is_decided(idx1, idx2) {
                        continue;
                    }
                    let key = Self::ordered_pair(idx1, idx2);
                    if !seen.insert(key) {
                        continue;
                    }
                    // Skip pairs already encoded as an assigned SAT atom or
                    // already requested (dedup, mirrors check_interface_equalities).
                    if let Some(&idx_eq) = self.eq_pair_index.get(&key) {
                        if self.assigns.contains_key(&idx_eq) {
                            continue;
                        }
                    }
                    if self.model_equality_already_requested(idx1, idx2) {
                        continue;
                    }
                    self.mark_model_equality_requested(idx1, idx2);
                    requests.push(ModelEqualityRequest {
                        lhs: idx1,
                        rhs: idx2,
                        reason: vec![TheoryLit::new(eq_term, true)],
                        implied: false,
                    });
                }
            }
        }

        (!requests.is_empty()).then_some(requests)
    }

    fn finite_store_chain_alias_summary(&self, term: TermId) -> Option<(TermId, Vec<TermId>)> {
        let mut current = term;
        let mut indices = Vec::new();

        for _ in 0..64 {
            let Some((base, idx, _val, _eq_path)) = self.find_store_through_eq(current) else {
                return (!indices.is_empty()).then_some((current, indices));
            };

            indices.push(idx);
            if base == current || self.same_equiv_class(base, current) {
                return None;
            }
            current = base;
        }

        None
    }

    fn store_chain_indices_are_decided(&self, lhs: &[TermId], rhs: &[TermId]) -> bool {
        let mut indices = Vec::with_capacity(lhs.len() + rhs.len());
        indices.extend_from_slice(lhs);
        indices.extend_from_slice(rhs);
        // Canonicalize to a set: sort + dedup. Duplicate indices are trivially
        // same-class (decided), so removing them cannot change the all-pairs
        // result, and a canonical key lets commuted store chains that share an
        // index universe hit the same cache entry.
        indices.sort_unstable_by_key(|t| t.0);
        indices.dedup();

        if indices.len() < 2 {
            return true;
        }
        if let Some(&decided) = self.store_chain_decided_cache.borrow().get(&indices) {
            return decided;
        }

        let mut decided = true;
        'outer: for i in 0..indices.len() {
            for j in (i + 1)..indices.len() {
                if !self.pair_is_decided(indices[i], indices[j]) {
                    decided = false;
                    break 'outer;
                }
            }
        }

        self.store_chain_decided_cache
            .borrow_mut()
            .insert(indices, decided);
        decided
    }

    /// Whether the index pair `(a, b)` is DECIDED: same equivalence class, OR
    /// known-distinct, OR affine-offset-distinct. Pure function of the current
    /// (per-`final_check`) theory state; memoized via `pairwise_decided_cache`
    /// (cleared at each `final_check` entry) because the store-chain guards
    /// evaluate it millions of times over only ~thousands of distinct pairs.
    ///
    /// Evaluation order matches the original inline predicate exactly, so the
    /// memoized result is identical to recomputing it.
    fn pair_is_decided(&self, a: TermId, b: TermId) -> bool {
        if a == b {
            return true;
        }
        let key = Self::ordered_pair(a, b);
        if let Some(&decided) = self.pairwise_decided_cache.borrow().get(&key) {
            return decided;
        }
        let decided = self.same_equiv_class(a, b)
            || self.known_distinct(a, b)
            || self.distinct_by_affine_offset(a, b);
        self.pairwise_decided_cache
            .borrow_mut()
            .insert(key, decided);
        decided
    }

    fn store_chain_reaches_equiv_class_from_endpoint(&self, term: TermId, target: TermId) -> bool {
        let mut current = term;

        for _ in 0..64 {
            let Some((base, _idx, _val, _eq_path)) = self.find_store_through_eq(current) else {
                return false;
            };
            if self.same_equiv_class(base, target) {
                return true;
            }
            if base == current || self.same_equiv_class(base, current) {
                return false;
            }
            current = base;
        }

        false
    }

    /// Check if two terms are in the same equivalence class.
    ///
    /// Uses the cached equivalence class map when available for O(1) lookup.
    fn same_equiv_class(&self, a: TermId, b: TermId) -> bool {
        if a == b {
            return true;
        }
        if self.equiv_class_cache_version == Some(self.eq_adj_version) {
            let class_a = self.equiv_class_map.get(&a);
            let class_b = self.equiv_class_map.get(&b);
            if let (Some(&ca), Some(&cb)) = (class_a, class_b) {
                return ca == cb;
            }
            // If either is not in eq_adj, they're singletons and not equal
            return false;
        }
        // Fall back to known_equal for non-cached path
        self.known_equal(a, b)
    }
}
