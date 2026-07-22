// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TheorySolver trait implementation for LIA.

use super::*;

impl TheorySolver for LiaSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        // Delegate to inner LRA solver so atom_index is populated.
        // Without this, LRA bound propagation cannot deduce implied atoms
        // for LIA problems (#4919).
        self.lra.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        debug_assert!(
            (literal.0 as usize) < self.terms.len(),
            "BUG: LIA assert_literal: term {} out of range (term store len={})",
            literal.0,
            self.terms.len()
        );

        // Any new assertion invalidates cached direct-enumeration models.
        self.direct_enum_witness = None;

        // Unwrap NOT: NOT(inner)=true means inner=false
        let (term, val) = unwrap_not(self.terms, literal, value);

        // Collect integer variables from this literal
        self.collect_integer_vars(term);

        // Track assertion for conflict generation
        self.asserted.push((term, val));
        // #C3: Detect a Boolean-constant atom asserted with the opposite
        // polarity once, here, rather than rescanning all of `asserted` on every
        // check. This is an immediate, assignment-independent contradiction.
        if let TermData::Const(Constant::Bool(b)) = self.terms.get(term) {
            if val != *b {
                let idx = self.asserted.len() - 1;
                self.const_bool_conflicts
                    .push((idx, TheoryLit { term, value: val }));
            }
        }
        // #C3b (#ground-arith-atom, 2026-07-12): the same immediate,
        // assignment-independent contradiction for a VARIABLE-FREE arithmetic
        // atom — `(= 30 20)` asserted true. Its linear form has no variables,
        // so the LRA relaxation records no constraint and `check()` answered
        // SAT: LIA claimed a ground false equality was satisfiable. That is a
        // completeness bug in its own right, and it also broke the CONFLICT
        // VERIFIER (`verify_lia_conflict_semantic` re-solves a conflict in a
        // fresh LiaSolver): a genuine one-literal array-theory conflict
        // `{(= 30 20) = true}` came back "satisfiable", so the split loop
        // fail-closed to Unknown rather than learn an "unverifiable" clause —
        // turning satisfiable 3-store QF_AUFLIA chains into unknown.
        if let Some(truth) = self.ground_arith_atom_truth(term) {
            if val != truth {
                let idx = self.asserted.len() - 1;
                self.const_bool_conflicts
                    .push((idx, TheoryLit { term, value: val }));
            }
        }
        // Keep the incremental assertion view in lockstep with `asserted` (#C1).
        self.assertion_view_cache.on_assert(self.terms, term, val);

        // Forward to LRA solver (which also handles NOT unwrapping)
        self.lra.assert_literal(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        tracing::debug!(
            asserted = self.asserted.len(),
            integer_vars = self.integer_vars.len(),
            gomory_iter = self.gomory_iterations,
            hnf_iter = self.hnf_iterations,
            "LIA check"
        );
        let result = self.check_inner();
        // #8147: Augment ALL conflicts (Unsat and UnsatWithFarkas) with shared
        // equality + Dioph reasons. The Unsat path (e.g. LRA trivial_conflict,
        // disequality check) can also miss shared equality reasons when the
        // conflict's bound reasons don't include pivoted-away slack variables.
        let result = match result {
            TheoryResult::UnsatWithFarkas(conflict) => {
                TheoryResult::UnsatWithFarkas(self.augment_farkas_with_shared_reasons(conflict))
            }
            TheoryResult::Unsat(lits) => {
                let conflict = TheoryConflict::new(lits);
                let augmented = self.augment_farkas_with_shared_reasons(conflict);
                TheoryResult::Unsat(augmented.literals)
            }
            other => other,
        };
        if matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ) {
            self.conflict_count += 1;
        }
        result
    }

    fn check_during_propagate(&mut self) -> TheoryResult {
        self.check_count += 1;
        tracing::debug!(
            asserted = self.asserted.len(),
            integer_vars = self.integer_vars.len(),
            "LIA check_during_propagate"
        );
        let result = self.check_during_propagate_inner();
        // #8147: Augment ALL conflicts with shared equality + Dioph reasons.
        let result = match result {
            TheoryResult::UnsatWithFarkas(conflict) => {
                TheoryResult::UnsatWithFarkas(self.augment_farkas_with_shared_reasons(conflict))
            }
            TheoryResult::Unsat(lits) => {
                let conflict = TheoryConflict::new(lits);
                let augmented = self.augment_farkas_with_shared_reasons(conflict);
                TheoryResult::Unsat(augmented.literals)
            }
            other => other,
        };
        if matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ) {
            self.conflict_count += 1;
        }
        result
    }

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    fn set_search_phase(&mut self, in_search: bool) {
        self.in_search_phase = in_search;
        self.dioph_bcp_unproductive_streak = 0;
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let props = self.lra.propagate();
        self.propagation_count += props.len() as u64;
        props
    }

    /// Forward buffered single-var disequality splits from the inner LRA solver
    /// so the DPLL(T) split loop can encode all of them in one round (#8762).
    fn drain_pending_diseq_splits(&mut self) -> Vec<DisequalitySplitRequest> {
        self.lra.drain_pending_diseq_splits()
    }

    fn push(&mut self) {
        assert_eq!(
            self.scopes.len(),
            self.cut_scopes.len(),
            "BUG: LIA push: scope stack ({}) and cut_scope stack ({}) out of sync",
            self.scopes.len(),
            self.cut_scopes.len()
        );
        self.scopes.push(self.asserted.len());
        // Mark the incremental view in the same transaction (#C1).
        self.assertion_view_cache.on_push();
        self.cut_scopes.push(self.learned_cuts.len());
        // Save cut-related state so pop() restores the outer scope's
        // iteration counters and seen-cut set (#3685).
        self.cut_state_scopes.push(CutScopeState {
            gomory_iterations: self.gomory_iterations,
            hnf_iterations: self.hnf_iterations,
            // #C7: O(1) trail mark instead of cloning the whole seen-cut set.
            seen_hnf_cuts_mark: self.seen_hnf_cuts_trail.len(),
            shared_eq_mark: self.shared_equalities.len(),
            shared_diseq_mark: self.shared_disequalities.len(),
        });
        self.lra.push();
        self.direct_enum_witness = None;
    }

    fn pop(&mut self) {
        if let Some(mark) = self.scopes.pop() {
            debug_assert!(
                mark <= self.asserted.len(),
                "BUG: LIA pop: scope mark {} exceeds asserted length {}",
                mark,
                self.asserted.len()
            );
            self.asserted.truncate(mark);
            // #C3: drop const-bool conflicts whose literal was just popped, so a
            // reported conflict reason is always a live literal (#8784). The Vec
            // is empty in the overwhelmingly common case, so retain is O(1).
            if !self.const_bool_conflicts.is_empty() {
                self.const_bool_conflicts.retain(|(idx, _)| *idx < mark);
            }
            // Truncate the incremental view in the SAME transaction as the
            // asserted-trail truncation (#C1, plan §3.4): otherwise
            // `conflict_reasons_all_live` could see stale view-derived
            // literals and publish a false-UNSAT conflict.
            self.assertion_view_cache.on_pop();
            self.lra.pop();
            self.direct_enum_witness = None;
            let cut_mark = self.cut_scopes.pop().unwrap_or(0);
            self.learned_cuts.truncate(cut_mark);
            // Restore cut state from the outer scope (#3685).
            // Previously these were hard-reset to 0/empty, losing the outer
            // scope's iteration progress and seen-cut deduplication set.
            let saved = self.cut_state_scopes.pop().unwrap_or_default();
            self.gomory_iterations = saved.gomory_iterations;
            self.hnf_iterations = saved.hnf_iterations;
            // #C7: undo only the HNF-cut keys inserted in this scope, restoring
            // the exact pre-push `seen_hnf_cuts` (#3685) without a per-push clone.
            while self.seen_hnf_cuts_trail.len() > saved.seen_hnf_cuts_mark {
                if let Some(key) = self.seen_hnf_cuts_trail.pop() {
                    self.seen_hnf_cuts.remove(&key);
                }
            }
            // #shared-eq-idempotent: drop exactly the keys whose trail entries
            // this pop removes, keeping `shared_eq_seen` in lockstep with the
            // trail. Insertion is deduped, so each key occurs at most once on
            // the trail and this undo is exact (same discipline as #C7's
            // `seen_hnf_cuts_trail`).
            while self.shared_equalities.len() > saved.shared_eq_mark {
                if let Some((lhs, rhs, _)) = self.shared_equalities.pop() {
                    let key = if lhs.0 <= rhs.0 {
                        (lhs, rhs)
                    } else {
                        (rhs, lhs)
                    };
                    self.shared_eq_seen.remove(&key);
                }
            }
            // Truncation changes the algebraic-detection input set; bump the
            // revision so the memo cannot alias a pop+push of equal length.
            self.shared_eq_revision += 1;
            self.shared_disequalities.truncate(saved.shared_diseq_mark);
            // #8124: Clear pending shared equality conflict on pop — the conflict
            // may have been derived from literals that are no longer asserted.
            self.pending_shared_eq_conflict = None;
            // #C8: Preserve the equality-derived Diophantine caches across pop.
            // They depend only on the asserted equality SET (captured by
            // `dioph_equality_key`), not on the inequality bounds that
            // branch-and-bound and BMC backtracking churn. Re-solving the full
            // Diophantine system after EVERY backtrack was a dominant per-check
            // cost on deep (depth>=2) BMC counterexamples. Instead, mark the
            // caches for re-validation; the unconditional `dioph_equality_key`
            // comparison in check()/check_during_propagate() reuses them when the
            // equality set is unchanged and drops+rebuilds them when it changed —
            // the exact staleness gate #3736 references. This mirrors what
            // `soft_reset` already does across a (more drastic) LRA reset
            // (parsing.rs:437-453).
            self.dioph_needs_revalidation = true;
            // The bound-tracking state records bounds Dioph ADDED to LRA; those
            // bounds were just popped, so it is stale. Clear it conservatively;
            // propagate_bounds_through_substitutions repopulates it in the new
            // scope (#8147).
            self.dioph_modified_bounds = false;
            self.dioph_bound_term_ids.clear();

            // AUDIT FIX [P]90: Clear propagated_equality_pairs on pop().
            // Without this, after backtracking, equalities that were previously propagated
            // won't be re-propagated even if they get re-established. This could cause
            // the N-O combination to miss conflicts in alternate search branches.
            self.propagated_equality_pairs.clear();
            self.propagated_disequality_pairs.clear();
            self.pending_equalities.clear();
        }
    }

    fn reset(&mut self) {
        self.lra.reset();
        self.integer_vars.clear();
        self.sorted_integer_vars.clear();
        // Fresh bound state → conservative full rescan (#C4).
        self.mark_int_bounds_all_dirty();
        // Variable index changed → dioph parse cache rows are stale (#C2).
        // (linear_cache/affine_cache stay: they depend only on the
        // append-only TermStore, not on assertions or the var index.)
        self.var_index_epoch += 1;
        self.int_constant_terms.clear();
        self.asserted.clear();
        self.const_bool_conflicts.clear();
        self.assertion_view_cache.clear();
        self.scopes.clear();
        self.cut_scopes.clear();
        self.cut_state_scopes.clear();
        self.direct_enum_witness = None;
        self.gomory_iterations = 0;
        self.hnf_iterations = 0;
        self.seen_hnf_cuts.clear();
        self.seen_hnf_cuts_trail.clear();
        self.learned_cuts.clear();
        self.dioph_equality_key.clear();
        self.dioph_needs_revalidation = false;
        self.dioph_safe_dependent_vars.clear();
        self.dioph_cached_substitutions.clear();
        self.dioph_cached_reasons.clear();
        self.dioph_modified_bounds = false;
        self.dioph_bound_term_ids.clear();
        self.pending_equalities.clear();
        self.propagated_equality_pairs.clear();
        self.propagated_disequality_pairs.clear();
        self.shared_equalities.clear();
        // INTERFACE-DIET: the withhold flag is sticky per-solve; a full reset is
        // a fresh solve, so the (now-empty) interface is genuinely complete again.
        self.hidden_interface = false;
        // #shared-eq-idempotent: the membership index mirrors the trail.
        self.shared_eq_seen.clear();
        self.shared_eq_revision += 1;
        self.detect_algebraic_cache = None;
        self.shared_disequalities.clear();
        self.pending_shared_eq_conflict = None;
        // #8628: Clear dioph_cached_modular_gcds that was previously missed,
        // causing stale modular GCD constraints to persist across resets.
        self.dioph_cached_modular_gcds.clear();
    }

    fn soft_reset(&mut self) {
        // Use clear_assertions which preserves learned HNF cuts
        self.clear_assertions();
    }

    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        let debug = self.debug_lia_nelson_oppen;

        // #8124: If assert_shared_equality detected an impossible constant
        // equality (e.g., 5 = 3 after substitution), report the conflict
        // immediately instead of proceeding with equality propagation.
        if let Some(conflict) = self.pending_shared_eq_conflict.take() {
            // #8784: Drop the conflict if any reason literal is stale.
            if !self.conflict_reasons_all_live(&conflict) {
                if debug {
                    safe_eprintln!(
                        "[LIA N-O] Dropping pending shared equality conflict: stale reason ({} lits)",
                        conflict.len()
                    );
                }
            } else {
                if debug {
                    safe_eprintln!(
                        "[LIA N-O] Reporting pending shared equality conflict ({} reasons)",
                        conflict.len()
                    );
                }
                return EqualityPropagationResult {
                    equalities: Vec::new(),
                    conflict: Some(conflict),
                    ..Default::default()
                };
            }
        }

        // Phase 1: Detect algebraic equalities from equality assertions and
        // shared equalities (#3581). This also performs Gaussian elimination
        // on the shared equality system to derive tight bounds for variables
        // whose values are uniquely determined (e.g., f(1) = 0 from
        // f(0) = x, f(1) = f(0) - x).
        let derived_tight_bounds = self.detect_algebraic_equalities(debug);

        // #8783: detect_algebraic_equalities may have discovered an inconsistent
        // system (e.g., `0 = 1` after Gaussian substitution of shared equalities)
        // and stored the conflict. Report it immediately — otherwise the caller
        // might treat the empty result as "fixpoint reached, no new equalities"
        // and move on to extract a spurious SAT model.
        if let Some(conflict) = self.pending_shared_eq_conflict.take() {
            // #8784: Drop the conflict if any reason literal is stale.
            if !self.conflict_reasons_all_live(&conflict) {
                if debug {
                    safe_eprintln!(
                        "[LIA N-O] Dropping algebraic-detection conflict: stale reason ({} lits)",
                        conflict.len()
                    );
                }
            } else {
                if debug {
                    safe_eprintln!(
                        "[LIA N-O] Reporting algebraic-detection conflict ({} reasons)",
                        conflict.len()
                    );
                }
                return EqualityPropagationResult {
                    equalities: Vec::new(),
                    conflict: Some(conflict),
                    ..Default::default()
                };
            }
        }

        // Phase 2: Collect variables with tight bounds (lower == upper)
        // These are variables whose value is uniquely determined
        let mut tight_bound_vars: Vec<(TermId, BigRational, Vec<TheoryLit>)> = Vec::new();

        for &var_term in &self.integer_vars {
            if let Some((Some(lower), Some(upper))) = self.lra.get_bounds(var_term) {
                // Check if bounds are equal (tight)
                if lower.value == upper.value && !lower.strict && !upper.strict {
                    // Collect reasons from both bounds
                    let mut reasons = Vec::new();
                    for (reason, val) in lower.reasons.iter().zip(lower.reason_values.iter()) {
                        reasons.push(TheoryLit::new(*reason, *val));
                    }
                    for (reason, val) in upper.reasons.iter().zip(upper.reason_values.iter()) {
                        if !reasons.iter().any(|r| r.term == *reason) {
                            reasons.push(TheoryLit::new(*reason, *val));
                        }
                    }

                    if debug {
                        safe_eprintln!(
                            "[LIA N-O] Tight bound: term {} = {} (reasons: {:?})",
                            var_term.0,
                            lower.value,
                            reasons
                        );
                    }

                    tight_bound_vars.push((var_term, lower.value.to_big(), reasons));
                }
            }
        }

        // Include derived tight bounds from Gaussian elimination (#3581).
        // These are variables whose values were determined by the shared
        // equality system but are not stored as LRA bounds.
        for (var, value, reasons) in derived_tight_bounds {
            // Avoid duplicates: only add if not already in LRA tight bounds
            if !tight_bound_vars.iter().any(|(t, _, _)| *t == var) {
                if debug {
                    safe_eprintln!(
                        "[LIA N-O] Derived tight bound: term {} = {} (reasons: {:?})",
                        var.0,
                        value,
                        reasons
                    );
                }
                tight_bound_vars.push((var, value, reasons));
            }
        }

        // Include integer constant terms with trivial tight bounds (#3581).
        // Constants like 0, 1, 5 have fixed values by definition. Without
        // including them, propagate_tight_bound_equalities cannot pair a
        // derived tight bound (e.g., f(1) = 0) with the constant 0 term,
        // because grouping by value requires both sides to be present.
        for (int_val, &const_term) in &self.int_constant_terms {
            let value = BigRational::from(int_val.clone());
            if !tight_bound_vars.iter().any(|(t, _, _)| *t == const_term) {
                tight_bound_vars.push((const_term, value, Vec::new()));
            }
        }

        // #8469: Discover disequalities from tight bounds before consuming tight_bound_vars.
        // Group by value for both equality and disequality discovery.
        let mut vars_by_value: HashMap<BigRational, Vec<(TermId, Vec<TheoryLit>)>> =
            HashMap::default();
        for (term, value, reasons) in &tight_bound_vars {
            vars_by_value
                .entry(value.clone())
                .or_default()
                .push((*term, reasons.clone()));
        }

        let mut new_disequalities = Vec::new();
        let mut sorted_groups: Vec<_> = vars_by_value.iter().collect();
        sorted_groups.sort_by_key(|(a, _)| *a);

        for i in 0..sorted_groups.len() {
            for j in (i + 1)..sorted_groups.len() {
                let (_, group_a) = &sorted_groups[i];
                let (_, group_b) = &sorted_groups[j];

                // For each pair of groups with different values, propagate
                // disequalities using anchor terms (first with non-empty reasons).
                for (term_a, reasons_a) in group_a.iter().take(1) {
                    if reasons_a.is_empty() {
                        continue;
                    }
                    for (term_b, reasons_b) in group_b.iter().take(1) {
                        if reasons_b.is_empty() {
                            continue;
                        }
                        // SOUNDNESS (#cross-sort-alias): never emit an
                        // ill-sorted disequality between terms of different
                        // sorts (mirrors propagate_tight_bound_equalities).
                        if self.terms.sort(*term_a) != self.terms.sort(*term_b) {
                            continue;
                        }
                        let pair = if term_a.0 < term_b.0 {
                            (*term_a, *term_b)
                        } else {
                            (*term_b, *term_a)
                        };
                        if self.propagated_disequality_pairs.contains(&pair) {
                            continue;
                        }
                        self.propagated_disequality_pairs.insert(pair);

                        let mut combined_reasons: Vec<TheoryLit> = reasons_a.clone();
                        for r in reasons_b {
                            if !combined_reasons
                                .iter()
                                .any(|e| e.term == r.term && e.value == r.value)
                            {
                                combined_reasons.push(*r);
                            }
                        }

                        if debug {
                            safe_eprintln!(
                                "[LIA N-O] Propagating disequality: term {} != term {} ({} reasons)",
                                term_a.0,
                                term_b.0,
                                combined_reasons.len()
                            );
                        }

                        new_disequalities.push(DiscoveredDisequality::new(
                            *term_a,
                            *term_b,
                            combined_reasons,
                        ));
                    }
                }
            }
        }

        let mut equalities = propagate_tight_bound_equalities(
            self.terms,
            tight_bound_vars,
            &mut self.propagated_equality_pairs,
        );

        // Phase 3: Implied DIFFERENCE equalities (completeness fix).
        //
        // Phase 2 only emits `a = b` when a variable is INDIVIDUALLY pinned
        // (lb == ub). It misses the case where only the DIFFERENCE `a - b` is
        // simplex-pinned to [0,0] — e.g. from `x <= y ∧ y <= x`, where the
        // tableau holds a row representing `x - y` pinned to 0 but neither `x`
        // nor `y` has a tight individual bound. Without emitting `x = y`, EUF
        // congruence never fires on `f(x), f(y)` and `x<=y ∧ y<=x ∧ f(x)!=f(y)`
        // returns `unknown` instead of `unsat`.
        //
        // SOUNDNESS (Lean invariant (ENT)): `find_entailed_difference_equalities`
        // returns a pair ONLY when `a - b` is forced to exactly 0 (lb == ub == 0,
        // non-strict) WITH a NON-EMPTY reason set. A zero-reason "forced" value
        // would be a simplex/default-model artifact (the #6282 regression
        // vector), NOT a genuine entailment; emitting it would flood EUF with
        // spurious equalities and cause false-UNSAT. Requiring non-empty
        // entailing reasons is exactly invariant (ENT): every T-model of the
        // asserted formula already satisfies `a = b`, so sharing it is
        // equisatisfiable. The reasons are the entailing literals, keeping EUF's
        // conflict clause valid under backtracking.
        //
        // Candidates are restricted to `integer_vars` (the shared/interface arith
        // terms), and the LRA helper further restricts to pairs already COUPLED
        // by asserted bounds (co-occurring in a tableau row), so this never runs
        // an O(n^2) difference query over unrelated program variables.
        {
            let candidates: Vec<TermId> = self.integer_vars.iter().copied().collect();
            let implied = self.lra.find_entailed_difference_equalities(&candidates);
            for (lhs, rhs, reasons) in implied {
                // Dedup against equalities already propagated this round / earlier.
                let pair = if lhs.0 < rhs.0 {
                    (lhs, rhs)
                } else {
                    (rhs, lhs)
                };
                if self.propagated_equality_pairs.contains(&pair) {
                    continue;
                }
                self.propagated_equality_pairs.insert(pair);

                if debug {
                    safe_eprintln!(
                        "[LIA N-O] Implied difference equality: term {} = term {} ({} reasons)",
                        lhs.0,
                        rhs.0,
                        reasons.len()
                    );
                }

                equalities.push(DiscoveredEquality::new(lhs, rhs, reasons));
            }
        }

        // Prepend any equalities from Phase 1 (algebraic detection)
        let mut algebraic = std::mem::take(&mut self.pending_equalities);
        algebraic.append(&mut equalities);

        // #qfuflia-a5-fixed-eqs (attempt 3, DIRECT bounds only): export
        // fixed-term equalities through the Nelson-Oppen interface (z3's
        // arith-fixed-eqs flow) restricted to pairs where BOTH vars are
        // pinned by their ASSERTED bounds — implied-bound fixings excluded
        // because their reason chains under-justify the equality and poison
        // conflict analysis (false UNSAT measured twice; see
        // direct_fixed_term_key).
        for req in self.lra.take_pending_fixed_term_model_equalities() {
            if req.reason.is_empty() {
                continue;
            }
            let (Some(&lv), Some(&rv)) = (
                self.lra.term_to_var().get(&req.lhs),
                self.lra.term_to_var().get(&req.rhs),
            ) else {
                continue;
            };
            // DIRECT-bounds fixings only: implied-bound pairs remain excluded
            // even with complete-flagged justifications — the false UNSAT on
            // xs-06-07-4-5-4-2 persisted with the completeness bool honored,
            // so the implied-bounds fixing DERIVATION itself over-claims for
            // this flow (engine audit recorded in task #5).
            // Per-side fixing evidence (#qfuflia-a5-fixed-eqs): either
            // DIRECT bounds (asserted lo == hi; reasons are the bound atoms)
            // or a SELF-VERIFIED row fixing (row equation over direct-fixed
            // support vars, entailment re-derived locally — the generic
            // implied-bound reason collector's completeness accounting was
            // measured to lie, so it is not consulted). Each side contributes
            // its own support atoms; unsupportable sides skip the pair.
            let mut extra_reasons: Vec<TheoryLit> = Vec::new();
            // Inferred-type helper (the Rational type is crate-private to
            // ay-lra): compute each side's fixed value or bail.
            macro_rules! side_value {
                ($v:expr) => {{
                    if let Some((val, _)) = self.lra.direct_fixed_term_key($v) {
                        Some(val)
                    } else if let Some((val, mut reasons)) =
                        self.lra.row_fixing_with_direct_support($v)
                    {
                        extra_reasons.append(&mut reasons);
                        Some(val)
                    } else {
                        None
                    }
                }};
            }
            let (Some(lval), Some(rval)) = (side_value!(lv), side_value!(rv)) else {
                continue;
            };
            if lval != rval {
                continue;
            }
            if std::env::var_os("AY_DEBUG_FIXED_EQS").is_some() {
                eprintln!(
                    "[fixed-eqs] export {}={} lhs={:?} rhs={:?} ",
                    req.lhs.0,
                    req.rhs.0,
                    self.lra.terms().get(req.lhs),
                    self.lra.terms().get(req.rhs),
                );
                for l in &req.reason {
                    eprintln!(
                        "[fixed-eqs]   reason {}={} {:?}",
                        l.term.0,
                        l.value,
                        self.lra.terms().get(l.term)
                    );
                }
            }
            let mut all_reasons = req.reason.clone();
            for lit in extra_reasons {
                if !all_reasons.contains(&lit) {
                    all_reasons.push(lit);
                }
            }
            algebraic.push(DiscoveredEquality::new(req.lhs, req.rhs, all_reasons));
        }

        EqualityPropagationResult {
            equalities: algebraic,
            disequalities: new_disequalities,
            ..Default::default()
        }
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        // Receive equality from another theory (EUF→LIA direction in Nelson-Oppen).
        // Add the equality constraint: lhs = rhs, which means lhs - rhs = 0.
        //
        // This allows LIA to use EUF-discovered equalities in its arithmetic reasoning.
        // For example, if EUF tells us (f 5) = -1, we add the constraint (f 5) - (-1) = 0,
        // which affects bounds on (f 5) in the simplex tableau.

        debug_assert!(
            (lhs.0 as usize) < self.terms.len(),
            "BUG: LIA assert_shared_equality: lhs term {} out of range (term store len={})",
            lhs.0,
            self.terms.len()
        );
        debug_assert!(
            (rhs.0 as usize) < self.terms.len(),
            "BUG: LIA assert_shared_equality: rhs term {} out of range (term store len={})",
            rhs.0,
            self.terms.len()
        );

        // #7451: Reject equalities involving non-arithmetic terms. In SLIA
        // problems, EUF can propagate String-sorted equalities (e.g., x = "hello")
        // to LIA. Without this guard, term_to_linear_coeffs treats String terms
        // as opaque LRA variables with value 0, causing propagate_equalities to
        // produce spurious cross-sort equalities (String = Int) → false UNSAT.
        let lhs_sort = self.terms.sort(lhs);
        let rhs_sort = self.terms.sort(rhs);
        if !matches!(lhs_sort, Sort::Int | Sort::Real)
            || !matches!(rhs_sort, Sort::Int | Sort::Real)
        {
            return;
        }

        // Register integer variables from both sides of the shared equality (#3581).
        // Without this, variables introduced only via shared equalities (e.g., UF
        // applications like f(0), f(1) and plain variables like x forwarded from
        // is_uf_int_equality) are not tracked in integer_vars. This means
        // propagate_equalities() never discovers their tight bounds, breaking
        // Nelson-Oppen equality propagation for chains like:
        //   f(0) = x, f(1) = f(0) - x → f(1) = 0
        self.collect_integer_vars(lhs);
        self.collect_integer_vars(rhs);

        // #8784: Mark EUF-originated reason literals as "cross-theory asserted"
        // in the underlying LRA solver so that later stale-reason guards
        // (which delegate to `LraSolver::conflict_literals_all_asserted`)
        // accept them as live. Without this, conflicts built from shared
        // equalities — e.g. the #8783 Case 0 algebraic-detection conflict
        // and `augment_farkas_with_shared_reasons` — would be flagged stale
        // whenever their reason atoms are asserted on EUF rather than on LIA.
        //
        // Done BEFORE the idempotence check: a repeat assertion of an equality
        // already on the trail may carry a DIFFERENT reason set, and those
        // literals must still be recorded as live or a later conflict built
        // from them would be wrongly discarded as stale.
        if !reason.is_empty() {
            self.lra.record_cross_theory_reasons_from_lits(reason);
        }

        // #shared-eq-idempotent: `a = b` asserted twice is the same constraint
        // as `a = b` asserted once. The Nelson-Oppen fixpoint re-asserts every
        // shared equality on every round, so without this check the trail grows
        // by one entry per equality per round forever, and each round pays to
        // re-scan a trail that carries no new information (and to re-assert an
        // identical bound into LRA). Deduping makes the fixpoint actually reach
        // a fixpoint. See `LiaSolver::shared_eq_seen`.
        //
        // The key is the UNORDERED pair: `assert_shared_equality(a, b)` and
        // `(b, a)` denote the same equality.
        let key = if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        if !self.shared_eq_seen.insert(key) {
            return;
        }

        // Store the shared equality for algebraic detection in propagate_equalities (#3581).
        self.shared_equalities.push((lhs, rhs, reason.to_vec()));
        self.shared_eq_revision += 1;

        // NOTE (#shared-eq-view-rebuild): do NOT call `invalidate_assertion_view()`
        // here. That does a FULL O(|asserted|) rebuild of the view — and the view
        // is a function of `self.asserted` ALONE, which a shared equality never
        // touches, so the rebuild reconstructs an IDENTICAL view. Its only real
        // effect was bumping the view epoch to invalidate the
        // `detect_algebraic_equalities` memo, and that memo's stamp already
        // includes `shared_eq_revision`, which this function just incremented.
        // In the Nelson-Oppen fixpoint (which re-asserts shared equalities every
        // round) the redundant rebuild made the loop quadratic in the assertion
        // count — the dominant cost of the incremental AUFLIA push/pop hang.

        let debug = self.debug_lia_nelson_oppen;
        if debug {
            safe_eprintln!(
                "[LIA N-O] Receiving shared equality: term {} = term {} (reason: {:?})",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        // Parse both terms into linear expressions
        let lhs_coeffs = self.term_to_linear_coeffs(lhs);
        let rhs_coeffs = self.term_to_linear_coeffs(rhs);

        // Build linear expression: lhs - rhs = 0
        // coeffs: var_term -> coefficient
        let mut combined_coeffs: HashMap<TermId, BigRational> = HashMap::default();
        let mut constant = BigRational::zero();

        // Add lhs coefficients (positive)
        for (var, coeff) in lhs_coeffs.vars {
            *combined_coeffs.entry(var).or_insert_with(BigRational::zero) += &coeff;
        }
        constant += &lhs_coeffs.constant;

        // Subtract rhs coefficients
        for (var, coeff) in rhs_coeffs.vars {
            *combined_coeffs.entry(var).or_insert_with(BigRational::zero) -= &coeff;
        }
        constant -= &rhs_coeffs.constant;

        // Remove zero coefficients
        combined_coeffs.retain(|_, c| !c.is_zero());

        // If expression is just a constant, check if it's zero
        if combined_coeffs.is_empty() {
            if constant.is_zero() {
                // lhs = rhs is trivially true, no constraint needed
                if debug {
                    safe_eprintln!("[LIA N-O]   Equality is trivially true (constant 0)");
                }
            } else {
                // lhs = rhs is impossible (constant != 0).
                // #8124: Store the conflict so it is reported via
                // propagate_equalities() / check(). Previously this was
                // silently dropped, causing Unknown instead of UNSAT.
                if debug {
                    safe_eprintln!(
                        "[LIA N-O]   Equality is impossible! Constant {} != 0 — storing conflict",
                        constant
                    );
                }
                let conflict_reasons: Vec<TheoryLit> = if reason.is_empty() {
                    // No reason literals — use the equality terms themselves.
                    vec![TheoryLit::new(lhs, true)]
                } else {
                    reason.to_vec()
                };
                debug_assert!(
                    !conflict_reasons.is_empty(),
                    "BUG: LIA assert_shared_equality: impossible constant equality \
                     with empty conflict reasons (lhs={lhs:?}, rhs={rhs:?}, constant={constant})"
                );
                self.pending_shared_eq_conflict = Some(conflict_reasons);
            }
            return;
        }

        // Assert the equality constraint: Σ(coeff_i * var_i) + constant = 0
        // This means: Σ(coeff_i * var_i) = -constant
        // We add dual bounds: expr <= 0 AND expr >= 0
        //
        // Pass ALL reason literals so conflict explanations are complete.
        // Previously only the first reason was tracked, causing false UNSAT
        // when cross-disequality split atoms were dropped (#4891).
        let reasons: Vec<(TermId, bool)> = if reason.is_empty() {
            vec![(lhs, true)]
        } else {
            reason.iter().map(|r| (r.term, r.value)).collect()
        };

        // Use the underlying LRA solver to add bounds
        // The LRA solver tracks variables by TermId, so we need to convert our expression
        // Sort by TermId for deterministic registration order (#2681)
        let mut sorted_coeffs: Vec<_> = combined_coeffs.iter().collect();
        sorted_coeffs.sort_by_key(|(&var, _)| var);
        for (&var, _coeff) in &sorted_coeffs {
            // Ensure the variable is registered with LRA
            self.lra.ensure_var_registered(var);
        }

        // Add the constraint expr = 0 (where expr = Σ(coeff * var) + constant)
        // This is equivalent to: -constant <= Σ(coeff * var) <= -constant
        let neg_constant = -&constant;
        self.lra
            .assert_linear_equality_with_reasons(&combined_coeffs, &neg_constant, &reasons);

        if debug {
            safe_eprintln!(
                "[LIA N-O]   Added constraint: {} vars, constant={}",
                combined_coeffs.len(),
                constant
            );
        }
    }

    fn assert_shared_disequality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        // Receive disequality from another theory (EUF→LIA direction in Nelson-Oppen).
        // When EUF asserts (not (= (g x) 5)), LIA needs to know lhs != rhs so it can
        // detect violations: if the LIA model satisfies lhs = rhs, a split or conflict
        // is generated (#5228).

        let debug = self.debug_lia_nelson_oppen;
        if debug {
            safe_eprintln!(
                "[LIA N-O] Receiving shared disequality: term {} != term {} (reason: {} lits)",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        // Register integer variables from both sides for Nelson-Oppen tracking (#3581).
        self.collect_integer_vars(lhs);
        self.collect_integer_vars(rhs);

        if !reason.is_empty() {
            self.lra.record_cross_theory_reasons_from_lits(reason);
        }
        self.shared_disequalities.push((lhs, rhs, reason.to_vec()));

        // #certora-diseq-epoch: a shared disequality changes neither `terms`
        // nor `asserted`, so the historical full view rebuild here recreated
        // byte-identical content — its only observable effect was the epoch
        // bump that invalidates the epoch-stamped memos (the same argument
        // that removed the rebuild from `assert_shared_equality`,
        // #shared-eq-view-rebuild). Keep exactly that effect at O(1). The
        // rebuild was ~35% of on-CPU time on the Certora QF_UFLIA VC family
        // (2026-07-14 sample profile).
        self.assertion_view_cache.bump_epoch();

        // Forward to the inner LRA solver's shared disequality trail.
        // LRA's disequality checking infrastructure (post-simplex) will evaluate
        // lhs - rhs in the model and generate a split or conflict if lhs = rhs.
        self.lra.assert_shared_disequality(lhs, rhs, reason);
    }

    fn supports_theory_aware_branching(&self) -> bool {
        // LIA is an arithmetic theory — theory atoms should be decided before
        // Tseitin encoding variables. Delegate to inner LRA solver.
        self.lra.supports_theory_aware_branching()
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        // Delegate to inner LRA solver for LP-model-consistent polarity.
        // Without this forwarding, UfLia/AufLia adapters get None (default)
        // for all atoms, causing polarity=true fallback instead of
        // model-consistent polarity (P1:122 finding 1).
        self.lra.suggest_phase(atom)
    }

    fn phase_hint_epoch(&self) -> Option<u64> {
        // `suggest_phase` above is a pure delegate to the inner LRA solver,
        // so its epoch (bumped exactly when the phase-hint cache / feasible
        // snapshot changes) fully covers suggestion change. Without this
        // forwarding the SAT seeder's epoch skip was dead on UF+LIA lanes
        // and every BCP quiescence re-scanned all theory atoms
        // (#certora-phase-epoch: ~19% of the solve on 10^5-atom files).
        //
        // SIZE-GATED: only report an epoch on giant instances. The skip is
        // value-exact (an unchanged epoch means identical suggestions) but
        // NOT trajectory-exact — a skipped re-seed no longer overwrites
        // phases that phase-saving flipped between quiescences — and the
        // every-quiescence re-seed trajectory is load-bearing for protected
        // crafted greens (measured: Hash hash_sat_03_11 flips sat->unknown
        // under the unconditional skip, 2/2 interleaved A/B rounds). Small
        // instances therefore keep the historical behavior bit-exactly
        // (`None` disables the skip); on 10^4+-atom industrial files the
        // O(atoms) re-scan is the wall and the skip is decisive.
        const PHASE_EPOCH_MIN_ATOMS: usize = 8192;
        if self.lra.registered_atom_count() < PHASE_EPOCH_MIN_ATOMS {
            return None;
        }
        self.lra.phase_hint_epoch()
    }

    fn sort_atom_index(&mut self) {
        // Forward to inner LRA solver to sort atoms by bound value for
        // O(log n) nearest-neighbor lookup in bound axiom generation.
        self.lra.sort_atom_index();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        // Call the inner implementation directly. The LRA trait method is
        // disabled (#8254) for pure-LRA to avoid ITE pathologies, but LIA
        // needs bound ordering axioms for integer transitivity chains.
        self.lra.generate_bound_axiom_terms_inner()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        // Same as above: bypass the disabled LRA trait method.
        self.lra.generate_incremental_bound_axioms_inner(atom)
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("lia_checks", self.check_count),
            ("lia_conflicts", self.conflict_count),
            ("lia_propagations", self.propagation_count),
            (
                "lia_affine_min_core_attempts",
                self.affine_min_core_attempts,
            ),
            (
                "lia_affine_min_core_successes",
                self.affine_min_core_successes,
            ),
            ("lia_detect_algebraic_calls", self.detect_algebraic_calls),
            (
                "lia_detect_algebraic_cache_hits",
                self.detect_algebraic_cache_hits,
            ),
        ]
    }
}

impl LiaSolver<'_> {
    /// True when `term` is built only from numeric constants and +/-/* (i.e.
    /// mentions no variable). Bounded depth: a deep expression simply fails the
    /// test, which only costs the fold, never soundness.
    fn term_is_constant_arith(&self, term: TermId, depth: u32) -> bool {
        if depth == 0 {
            return false;
        }
        match self.terms.get(term) {
            TermData::Const(_) => true,
            TermData::App(sym, args) if matches!(sym.name(), "+" | "-" | "*") => args
                .iter()
                .all(|&a| self.term_is_constant_arith(a, depth - 1)),
            _ => false,
        }
    }

    /// Truth value of a VARIABLE-FREE arithmetic atom (`=`, `<=`, `<`, `>=`,
    /// `>`) over integer constants, or `None` when the atom mentions a
    /// variable / is not one of those relations. Used by the `#C3b` immediate
    /// contradiction check.
    fn ground_arith_atom_truth(&self, term: TermId) -> Option<bool> {
        let TermData::App(sym, args) = self.terms.get(term) else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let rel = sym.name();
        if !matches!(rel, "=" | "<=" | "<" | ">=" | ">") {
            return None;
        }
        // Cheap variable-free pre-check BEFORE the (relatively costly) linear
        // parse: this runs on EVERY asserted arithmetic atom, and the atoms we
        // can fold are exactly the constant-only ones.
        if !self.term_is_constant_arith(args[0], 8) || !self.term_is_constant_arith(args[1], 8) {
            return None;
        }
        let lhs = self.term_to_linear_coeffs(args[0]);
        let rhs = self.term_to_linear_coeffs(args[1]);
        if !lhs.vars.is_empty() || !rhs.vars.is_empty() {
            return None;
        }
        let diff = &lhs.constant - &rhs.constant; // lhs - rhs
        Some(match rel {
            "=" => diff.is_zero(),
            "<=" => diff <= BigRational::zero(),
            "<" => diff < BigRational::zero(),
            ">=" => diff >= BigRational::zero(),
            ">" => diff > BigRational::zero(),
            _ => return None,
        })
    }
}
