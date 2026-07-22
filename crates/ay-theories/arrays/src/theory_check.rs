// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array theory check implementation.
//!
//! Dispatches to sub-check methods (ROW1, ROW2, self-store, etc.) and batches
//! their results. Extracted from `theory_impl.rs` to keep each file under 500 lines.

use super::*;

const REQUESTED_EQS_SOFT_CAP: usize = 8_192;

impl ArraySolver<'_> {
    /// Core check logic: dispatches to sub-check methods and batches results.
    ///
    /// Each sub-check returns `Option<TheoryResult>`:
    /// - `Unsat` conflicts are returned immediately
    /// - `NeedLemmas` are batched and returned together
    /// - `NeedModelEquality` requests are batched at lower priority
    pub(crate) fn check_impl(&mut self) -> TheoryResult {
        // #8615: Early exit if the external interrupt flag is set. Array theory
        // check can be very expensive with many sub-checks; returning Unknown
        // allows the DPLL(T) loop to detect the interrupt.
        if self.is_interrupted() {
            return TheoryResult::Unknown;
        }

        self.check_count += 1;

        // #8605: Cap monotonically-growing dedup sets to prevent unbounded memory.
        // requested_model_eqs and requested_interface_eqs persist across pop()
        // and are only cleared on reset(). For long-running solves, they can
        // accumulate O(terms^2) entries. Clearing them is safe: re-requesting
        // an already-created equality is a no-op in the DPLL(T) layer.
        if self.requested_model_eqs.len() > REQUESTED_EQS_SOFT_CAP {
            self.requested_model_eqs.clear();
            self.requested_model_eqs.shrink_to_fit();
        }
        if self.requested_interface_eqs.len() > REQUESTED_EQS_SOFT_CAP {
            self.requested_interface_eqs.clear();
            self.requested_interface_eqs.shrink_to_fit();
        }

        // Invariant: scope markers are within trail bounds
        debug_assert!(
            self.scopes.iter().all(|&mark| mark <= self.trail.len()),
            "arrays: scope marker exceeds trail length"
        );

        // Invariant: eq_pair_index keys are canonically ordered (min, max)
        debug_assert!(
            self.eq_pair_index.keys().all(|(a, b)| a <= b),
            "arrays: eq_pair_index has non-canonical key ordering"
        );

        // Invariant: diseq_set keys are canonically ordered
        debug_assert!(
            self.diseq_set.iter().all(|(a, b)| a <= b),
            "arrays: diseq_set has non-canonical key ordering"
        );

        // Invariant: external_diseqs are canonically ordered
        debug_assert!(
            self.external_diseqs.iter().all(|(a, b)| a <= b),
            "arrays: external_diseqs has non-canonical key ordering"
        );

        // Invariant: select_cache entries are valid select terms
        debug_assert!(
            self.select_cache.iter().all(|(term_id, _)| {
                matches!(self.terms.get(*term_id), TermData::App(sym, args) if sym.name() == "select" && args.len() == 2)
            }),
            "arrays: select_cache contains non-select terms"
        );

        self.populate_caches();

        // (#6820 Step 3) Equivalence class cache is now built lazily on demand
        // by methods that need it (get_equiv_class, known_distinct_via_equiv_classes).
        // No need to force a BFS at the top of every check() call.

        // #6694: Restore early-return for direct Unsat conflicts, but keep
        // batching for stable clause-producing results and model-equality
        // requests.
        let mut batched_lemmas: Vec<TheoryLemma> = Vec::new();
        let mut model_eq_requests: Vec<ModelEqualityRequest> = Vec::new();

        // Check ROW1: select(store(a, i, v), i) = v
        if let Some(result) = self.check_row1() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: ROW1 conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(count = lemmas.len(), "arrays check: ROW1 batch lemmas");
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: ROW1 non-sat result");
                }
            }
        }

        // Check self-store: store(a, i, v) = a implies select(a, i) = v (Fix for #920)
        if let Some(result) = self.check_self_store() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: self-store conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: self-store batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: self-store non-sat result");
                }
            }
        }

        // #8141: Lazily generate ROW2 down axioms. Previously, registration
        // eagerly queued all store-select ROW2 pairs. Now we generate them on
        // demand with a budget to avoid overwhelming the SAT solver.
        self.generate_lazy_row2_axioms();

        // Check ROW2 downward: queued `(store, select)` pairs
        if let Some(result) = self.check_row2() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: ROW2 conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(count = lemmas.len(), "arrays check: ROW2 batch lemmas");
                    batched_lemmas.extend(lemmas);
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!("arrays check: ROW2 NeedModelEquality");
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    tracing::debug!(count = reqs.len(), "arrays check: ROW2 NeedModelEqualities");
                    model_eq_requests.extend(reqs);
                }
                _ => {
                    tracing::debug!("arrays check: ROW2 non-sat result");
                }
            }
        }

        // #8785: In combined mode, broad finite-support store-chain checks are
        // deferred to final_check(), but singleton support is a precise split
        // that can unlock the search immediately. Surface only that narrow
        // case here so storecomm-style rows do not spend many rounds before the
        // decisive read-index equality is even requested.
        if self.defer_expensive_checks {
            if let Some(result) = self.check_store_chain_select_difference_witness_singleton() {
                match result {
                    TheoryResult::Unsat(ref _reasons) => {
                        tracing::debug!("arrays check: singleton store-chain support conflict");
                        #[cfg(debug_assertions)]
                        self.validate_conflict_explanation(_reasons);
                        self.conflict_count += 1;
                        return result;
                    }
                    TheoryResult::NeedLemmas(lemmas) => {
                        tracing::debug!(
                            count = lemmas.len(),
                            clauses = ?lemmas.iter().map(|l| &l.clause).collect::<Vec<_>>(),
                            "arrays check: singleton store-chain support lemmas"
                        );
                        batched_lemmas.extend(lemmas);
                    }
                    TheoryResult::NeedModelEquality(req) => {
                        tracing::debug!(
                            "arrays check: singleton store-chain support NeedModelEquality"
                        );
                        model_eq_requests.push(req);
                    }
                    TheoryResult::NeedModelEqualities(reqs) => {
                        tracing::debug!(
                            count = reqs.len(),
                            "arrays check: singleton store-chain support NeedModelEqualities"
                        );
                        model_eq_requests.extend(reqs);
                    }
                    _ => {
                        tracing::debug!("arrays check: singleton store-chain support non-sat");
                    }
                }
            }
        }

        // Expensive O(n²) checks: deferred to final_check() when the combined
        // solver will call it at fixpoint. In standalone mode (unit tests, or when
        // defer_expensive_checks is false), run them here for correctness (#6282).
        if !self.defer_expensive_checks {
            if let Some(conflict) =
                self.check_expensive_axioms(&mut batched_lemmas, &mut model_eq_requests)
            {
                return conflict;
            }
        }

        // Check const-array reads (event-driven via pending_const_reads queue)
        if let Some(result) = self.check_const_array_read() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: const-array-read conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: const-array-read batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: const-array-read non-sat result");
                }
            }
        }

        // Check select-map axioms (#8533): select(map[f](a1,...,an), i) = f(select(a1,i),...,select(an,i))
        if let Some(result) = self.check_select_map() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: select-map conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: select-map batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: select-map non-sat result");
                }
            }
        }

        // Check default-const axioms (#8598): default(X) = v when X =_E const-array(v)
        if let Some(result) = self.check_default_const() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: default-const conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: default-const batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: default-const non-sat result");
                }
            }
        }

        // Check select-as-array axioms (#8598): select(as-array[f], i) = f(i)
        if let Some(result) = self.check_select_as_array() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: select-as-array conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return result;
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: select-as-array batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: select-as-array non-sat result");
                }
            }
        }

        // Deduplicate batched ROW2 lemmas: multiple ROW2 pairs may produce
        // overlapping lemmas. Canonicalize clause literal order then deduplicate.
        for lemma in &mut batched_lemmas {
            lemma.clause.sort_by_key(|lit| (lit.term.0, lit.value));
        }
        let pre_dedup = batched_lemmas.len();
        {
            let mut seen = HashSet::default();
            batched_lemmas.retain(|lemma| seen.insert(lemma.clause.clone()));
        }

        // Also filter out lemmas already emitted in a prior check() call.
        batched_lemmas.retain(|lemma| !self.applied_theory_lemmas.contains(&lemma.clause));

        if pre_dedup != batched_lemmas.len() {
            tracing::debug!(
                pre_dedup,
                post_dedup = batched_lemmas.len(),
                "arrays check: deduplicated batched lemmas"
            );
        }

        // Return batched ROW2 lemmas (highest priority — they constrain search).
        if !batched_lemmas.is_empty() {
            self.rollback_unreturned_model_equality_requests(&model_eq_requests);
            tracing::debug!(
                count = batched_lemmas.len(),
                clauses = ?batched_lemmas.iter().map(|l| &l.clause).collect::<Vec<_>>(),
                "arrays check: returning batched ROW2 lemmas"
            );
            return TheoryResult::NeedLemmas(batched_lemmas);
        }

        if !model_eq_requests.is_empty() {
            return match model_eq_requests.len() {
                1 => TheoryResult::NeedModelEquality(
                    model_eq_requests
                        .pop()
                        .expect("invariant: len checked above"),
                ),
                _ => TheoryResult::NeedModelEqualities(model_eq_requests),
            };
        }

        tracing::debug!("arrays check: sat");
        TheoryResult::Sat
    }

    /// Run expensive O(n²) axiom checks that are deferred to final_check() in
    /// combined solver mode. Returns `Some(conflict)` on Unsat for early exit.
    fn check_expensive_axioms(
        &mut self,
        batched_lemmas: &mut Vec<TheoryLemma>,
        model_eq_requests: &mut Vec<ModelEqualityRequest>,
    ) -> Option<TheoryResult> {
        // ROW2 upward (axiom 2b)
        if let Some(result) = self.check_row2_upward_with_guidance() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: ROW2-upward conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: ROW2-upward batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!("arrays check: ROW2-upward NeedModelEquality");
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    tracing::debug!(
                        count = reqs.len(),
                        "arrays check: ROW2-upward NeedModelEqualities"
                    );
                    model_eq_requests.extend(reqs);
                }
                _ => {}
            }
        }

        // ROW2 extended via store chain following
        if let Some(result) = self.check_row2_extended() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: ROW2-extended conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: ROW2-extended batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: ROW2-extended non-sat result");
                }
            }
        }

        // Store-permutation exact-select conflicts (#8785).
        if let Some(result) = self.check_store_permutation_select_conflicts() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: store-permutation-select conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: store-permutation-select batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: store-permutation-select non-sat result");
                }
            }
        }

        // Nested select conflicts
        if let Some(result) = self.check_nested_select_conflicts() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: nested-select conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: nested-select batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: nested-select non-sat result");
                }
            }
        }

        // Check store chain resolution
        if let Some(result) = self.check_store_chain_resolution() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: store-chain conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: store-chain batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: store-chain non-sat result");
                }
            }
        }

        // Check conflicting store equalities
        if let Some(result) = self.check_conflicting_store_equalities() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: conflicting-store-eq conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: conflicting-store-eq batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: conflicting-store-eq non-sat result");
                }
            }
        }

        // Check disjunctive store-target equalities (#8785):
        // store(base, i, v) = target and store(base, j, w) = target imply
        // i = j OR base = target. In deferred mode this runs from final_check();
        // in standalone/non-deferred mode, surface the same guarded lemma here.
        if let Some(result) = self.check_disjunctive_store_target_equalities() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: disjunctive-store-target conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: disjunctive-store-target batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                TheoryResult::NeedModelEquality(req) => {
                    tracing::debug!("arrays check: disjunctive-store-target NeedModelEquality");
                    model_eq_requests.push(req);
                }
                TheoryResult::NeedModelEqualities(reqs) => {
                    tracing::debug!(
                        count = reqs.len(),
                        "arrays check: disjunctive-store-target NeedModelEqualities"
                    );
                    model_eq_requests.extend(reqs);
                }
                _ => {
                    tracing::debug!("arrays check: disjunctive-store-target non-sat result");
                }
            }
        }

        // Check array equality implications
        if let Some(result) = self.check_array_equality() {
            match result {
                TheoryResult::Unsat(ref _reasons) => {
                    tracing::debug!("arrays check: array-equality conflict");
                    #[cfg(debug_assertions)]
                    self.validate_conflict_explanation(_reasons);
                    self.conflict_count += 1;
                    return Some(result);
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    tracing::debug!(
                        count = lemmas.len(),
                        "arrays check: array-equality batch lemmas"
                    );
                    batched_lemmas.extend(lemmas);
                }
                _ => {
                    tracing::debug!("arrays check: array-equality non-sat result");
                }
            }
        }

        None
    }
}
