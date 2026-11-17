// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `NiaSolver`.
//!
//! Implements the DPLL(T) theory interface for the nonlinear integer arithmetic theory.

use super::*;

impl TheorySolver for NiaSolver<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.bounded_enum_model = None;
        self.bounded_enum_bool_model.clear();
        // #nia-mccormick-contracted-bounds: contracted endpoints are
        // justified by the asserted trail that produced them.
        self.contracted_bounds.clear();
        self.contracted_bound_reasons.clear();
        // Undo any tentative patch before asserting new literals --
        // assertions must go into the real scope, not the patch scope.
        self.undo_tentative_patch();

        // Unwrap NOT: NOT(inner)=true means inner=false
        let (term, val) = match self.terms.get(literal) {
            TermData::Not(inner) => (*inner, !value),
            _ => (literal, value),
        };

        // Track assertion for conflict generation
        self.asserted.push((term, val));
        // Track asserted atoms for suggest_decision_atom (#8453, clauseSMT)
        self.asserted_atom_set.insert(term);

        // Collect integer variables for branch-and-bound
        self.collect_integer_vars(term);

        // Scan for and register nonlinear terms
        self.collect_nonlinear_terms(term);

        // Extract and record sign constraints from comparisons with zero
        if let Some((subject, constraint)) = self.extract_sign_constraint(term, val) {
            if self.debug {
                safe_eprintln!(
                    "[NIA] Recording sign constraint: subject={:?}, constraint={:?}, from assertion {:?}={}",
                    subject, constraint, term, val
                );
            }
            self.record_sign_constraint(subject, constraint, term);
        }

        // Delegate to LIA solver
        self.lia.assert_literal(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.bounded_enum_model = None;
        self.bounded_enum_bool_model.clear();
        self.contracted_bounds.clear();
        self.contracted_bound_reasons.clear();
        self.last_unsat_certificate = None;
        self.check_count += 1;
        tracing::debug!(
            asserted = self.asserted.len(),
            monomials = self.monomials.len(),
            "NIA check"
        );

        if self.debug {
            safe_eprintln!(
                "[NIA] check() called with {} assertions",
                self.asserted.len()
            );
        }

        // Undo any stale tentative patch from a previous check --
        // the SAT solver may have backtracked or asserted new literals.
        self.undo_tentative_patch();

        // clauseSMT Technique 2 (#8453): update feasible sets for arithmetic
        // propagation branching before entering the check loop. This
        // classifies variables as blocked/fixed/narrowed to guide branching.
        self.update_feasible_sets();

        maybe_grow_nia_stack(|| self.nia_check_loop())
    }

    /// The clausal local search over the original assertions
    /// (#nia-clausal-sls), offered when the split loop is about to give up
    /// on a monotone integer split walk (#split-walk-sat-fallback). The
    /// check loop reaches this lane only once its refinement stalls; a check
    /// that forwards the inner LIA's `NeedSplit` at once never does, and the
    /// split loop's oscillation guard then ends the search `unknown` within
    /// milliseconds (VeryMax Ex2.04 p21079). SAT-only: `true` means the
    /// witness passed `eval_formula_exact` on every root assertion.
    fn try_sat_before_split_giveup(&mut self) -> bool {
        matches!(self.try_local_search_lane(), Some(TheoryResult::Sat))
    }

    /// The same lane before a stale request's `Sat` goes to the model gate
    /// (#stale-accept-sat-lane). The check loop forwards the inner LIA's
    /// model equalities when its point violates an asserted disequality
    /// (#nia-diseq-model-eq); when the split loop has already encoded every
    /// one of them it accepts the round as `Sat`, and the gate rejects the
    /// point (AProVE 2467769011678516224: `unknown` in 2 s, while the
    /// pre-precision search reached this lane through its stall path and
    /// answered `sat`). Runs only when the model this solver would report
    /// (a pending enumeration witness included) provably falsifies a root
    /// assertion — a point the evaluator cannot refute is left exactly as it
    /// is — and only an exactly verified witness replaces it.
    fn try_sat_before_stale_accept(&mut self) -> bool {
        if !self.reported_model_falsifies_a_root() {
            return false;
        }
        matches!(self.try_local_search_lane(), Some(TheoryResult::Sat))
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let props = self.lia.propagate();
        self.propagation_count += props.len() as u64;
        props
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        let mut stats = vec![
            ("nia_checks", self.check_count),
            ("nia_conflicts", self.conflict_count),
            ("nia_propagations", self.propagation_count),
            ("nia_tangent_lemmas", self.tangent_lemma_count),
            ("nia_patches", self.patch_count),
            ("nia_sign_cuts", self.sign_cut_count),
            ("nia_unsat_with_guesses", self.unsat_with_guesses_count),
            ("nia_feasible_set_computations", self.feasible_set_count),
            ("nia_blocked_vars", self.blocked_vars.len() as u64),
            ("nia_fixed_vars", self.fixed_vars.len() as u64),
        ];
        stats.extend(self.lia.collect_statistics());
        stats
    }

    fn push(&mut self) {
        self.bounded_enum_model = None;
        self.bounded_enum_bool_model.clear();
        // Undo tentative patch scope before creating a new real scope
        self.undo_tentative_patch();
        self.scopes
            .push((self.asserted.len(), self.div_purifications.len()));
        // Save sign constraint trail mark for efficient pop (#8626).
        // On pop, we replay the trail backwards to undo additions.
        self.sign_constraint_trail_marks
            .push(self.sign_constraint_trail.len());
        // #3735: Start a new monomial trail scope. Monomials registered during
        // this scope will be removed on pop().
        self.monomial_trail.push(Vec::new());
        self.lia.push();
        // Reset feasible sets on push — they are recomputed on each check()
        self.reset_feasible_sets();
    }

    fn pop(&mut self) {
        self.bounded_enum_model = None;
        self.bounded_enum_bool_model.clear();
        self.contracted_bounds.clear();
        self.contracted_bound_reasons.clear();
        // Undo tentative patch scope before popping the real scope
        self.undo_tentative_patch();
        if let Some((assert_mark, div_mark)) = self.scopes.pop() {
            self.asserted.truncate(assert_mark);
            // Keep the SOS fragment cache aligned with the truncated
            // asserted set (entries are 1:1 by index).
            self.sos_fragment_cache
                .borrow_mut()
                .truncate_to_asserted(&self.asserted);
            self.div_purifications.truncate(div_mark);
            // Rebuild asserted_atom_set from the truncated asserted list (#8453)
            self.asserted_atom_set.clear();
            for &(atom, _) in &self.asserted {
                self.asserted_atom_set.insert(atom);
            }
        }
        // Undo sign constraint additions from the popped scope (#8626).
        // Replay the trail backwards: pop the last element from each inner Vec.
        // If the inner Vec becomes empty, remove the key entirely.
        if let Some(mark) = self.sign_constraint_trail_marks.pop() {
            while self.sign_constraint_trail.len() > mark {
                if let Some(entry) = self.sign_constraint_trail.pop() {
                    match entry {
                        SignConstraintTrailEntry::Monomial(key) => {
                            if let Some(vec) = self.sign_constraints.get_mut(&key) {
                                vec.pop();
                                if vec.is_empty() {
                                    self.sign_constraints.remove(&key);
                                }
                            }
                        }
                        SignConstraintTrailEntry::Variable(var) => {
                            if let Some(vec) = self.var_sign_constraints.get_mut(&var) {
                                vec.pop();
                                if vec.is_empty() {
                                    self.var_sign_constraints.remove(&var);
                                }
                            }
                        }
                    }
                }
            }
        }
        // #3735: Remove monomials registered during the popped scope.
        if let Some(trail) = self.monomial_trail.pop() {
            for (vars_key, aux_var) in trail {
                self.monomials.remove(&vars_key);
                self.aux_to_monomial.remove(&aux_var);
            }
        }
        // #nia-congruence: clear the per-scope congruence dedup set. The inner
        // LIA truncates its `shared_equalities` on pop, so any congruence
        // equalities added under this scope are gone; re-deriving them (sound)
        // on the next check is correct.
        self.congruence_linked.clear();
        // #nia-zero-bound: same discipline for the zero-bound lemma dedup set
        // — the inner LIA pop retracts cuts added under this scope, and any
        // re-derivation is re-justified from the then-current assertions.
        self.zero_bound_emitted.clear();
        self.box_bound_emitted.clear();
        self.zero_product_emitted.clear();
        // #nia-groebner: same discipline for the derived-equality dedup set.
        self.groebner_emitted.clear();
        self.lia.pop();
        // Reset feasible sets on pop — stale sets from the previous level
        // would include constraints that have been retracted.
        self.reset_feasible_sets();
    }

    fn reset(&mut self) {
        *self.sos_fragment_cache.borrow_mut() = Default::default();
        self.asserted.clear();
        self.scopes.clear();
        self.monomials.clear();
        self.aux_to_monomial.clear();
        self.sign_constraints.clear();
        self.var_sign_constraints.clear();
        self.sign_constraint_trail.clear();
        self.sign_constraint_trail_marks.clear();
        self.monomial_trail.clear();
        self.div_purifications.clear();
        self.bounded_enum_model = None;
        self.bounded_enum_bool_model.clear();
        self.contracted_bounds.clear();
        self.contracted_bound_reasons.clear();
        self.tentative_depth = 0;
        self.tentative_guess_count = 0;
        self.reset_feasible_sets();
        self.registered_atoms.clear();
        self.asserted_atom_set.clear();
        self.sat_atoms.clear();
        self.congruence_linked.clear();
        self.zero_bound_emitted.clear();
        self.box_bound_emitted.clear();
        self.zero_product_emitted.clear();
        self.groebner_emitted.clear();
        self.lia.reset();
    }

    /// Forward shared equalities from EUF to the underlying LIA solver.
    ///
    /// Required for UF+NIA theory combination (#4525). Without this,
    /// NIA ignores EUF equalities and can assign inconsistent values
    /// to UF function applications (e.g., f(x)=1 and f(y)=2 when x=y).
    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.lia.assert_shared_equality(lhs, rhs, reason);
    }

    /// Forward shared disequalities from EUF to the underlying LIA solver.
    ///
    /// Required for UF+NIA theory combination (#4525).
    fn assert_shared_disequality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.lia.assert_shared_disequality(lhs, rhs, reason);
    }

    /// Forward Farkas semantic check support to the underlying LIA solver.
    /// Ported from NRA (#8453).
    fn supports_farkas_semantic_check(&self) -> bool {
        self.lia.supports_farkas_semantic_check()
    }

    /// Forward equality propagation to the underlying LIA solver.
    /// Required for Nelson-Oppen theory combination to discover
    /// implicit equalities from arithmetic constraints. Ported from NRA (#8453).
    fn propagate_equalities(&mut self) -> ay_core::EqualityPropagationResult {
        self.lia.propagate_equalities()
    }

    /// Forward atom internalization to the underlying LIA solver.
    /// Enables early interval propagation from atom parsing.
    /// Ported from NRA (#8453).
    fn internalize_atom(&mut self, term: TermId) {
        self.lia.internalize_atom(term);
        // clauseSMT (#8453): track all registered atoms for suggest_decision_atom.
        // This lets us find unassigned atoms involving blocked/fixed variables.
        self.registered_atoms.push(term);
        // Pre-scan for nonlinear terms so feasible-set analysis can extract
        // linear univariate forms from atoms before they are asserted.
        self.collect_nonlinear_terms(term);
    }

    /// clauseSMT Technique 2 (#8453): use feasible-set information to
    /// suggest phases that are consistent with arithmetic feasibility.
    /// If we can compute a feasible set for this atom, suggest the phase
    /// that keeps the feasible set non-empty.
    ///
    /// #nonlinear-phase-hints: `feasible_set_phase` is the allocation-free,
    /// value-exact form of that decision (its doc carries the derivation); the
    /// previous two-feasible-set body is `feasible_set_phase_reference` and
    /// every debug build checks the two agree on every call.
    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        // Per-epoch memo (see the `phase_memo` field): suggestions are a
        // pure function of the state `phase_state_epoch` covers, so a hit
        // returns exactly what recomputation would. The borrow is dropped
        // before computing, so the debug reference check below still runs
        // on every fresh computation.
        let epoch = self.lia.lra_solver().phase_state_epoch();
        {
            let memo = self.phase_memo.borrow();
            if memo.0 == Some(epoch) {
                if let Some(value) = memo.1.get(&atom) {
                    return *value;
                }
            }
        }
        let phase = self.feasible_set_phase(atom);
        debug_assert_eq!(
            phase,
            self.feasible_set_phase_reference(atom),
            "feasible_set_phase diverged from its reference on atom {atom:?}"
        );
        let phase = if phase.is_some() {
            phase
        } else {
            self.lia.suggest_phase(atom)
        };
        let mut memo = self.phase_memo.borrow_mut();
        if memo.0 != Some(epoch) {
            memo.0 = Some(epoch);
            memo.1.clear();
        }
        memo.1.insert(atom, phase);
        phase
    }

    /// NIA is an arithmetic theory -- theory atoms should be decided before
    /// Tseitin encoding variables. Additionally, the clauseSMT feasible-set
    /// look-ahead (#8453) provides high-quality phase suggestions for
    /// nonlinear constraints that VSIDS alone cannot discover.
    fn register_atom(&mut self, atom: TermId) {
        // Count the SAT-visible vocabulary for the phase-epoch gate
        // (#nonlinear-phase-hints). Nothing else changes: the atom is still
        // parsed by the wrapped solver only when it is first asserted.
        self.sat_atoms.insert(atom);
    }

    fn phase_hint_epoch(&self) -> Option<u64> {
        // `suggest_phase` above is a function of the immutable term store and
        // of what the wrapped LIA's LRA exposes — `has_value` / `value_sign`
        // (columns, the assignment, the bounds through the materialisation
        // delta) for the feasible-set look-ahead, then `suggest_phase` (phase
        // cache, snapshot, registered atoms, `last_simplex_feasible`) for the
        // fallback — and `LraSolver::phase_state_epoch` advances on every
        // mutation of each of those (its doc enumerates the sites). So an
        // unchanged epoch means every suggestion is unchanged: value-exact.
        // The DPLL extension's debug canary re-derives every hint on a
        // skipped seed and asserts exactly that.
        //
        // SIZE-GATED at the same floor, for the same reason, as
        // `LiaSolver::phase_hint_epoch` (#certora-phase-epoch): the skip is
        // value-exact but not trajectory-exact — a skipped re-seed no longer
        // overwrites phases that phase-saving flipped between quiescences —
        // and small crafted greens were measured to depend on that trajectory.
        // The gate counts the atoms the DPLL layer registered (`sat_atoms`),
        // not the wrapped solver's `registered_atom_count`, because this lane
        // registers atoms with the linear solver only on first assertion.
        const PHASE_EPOCH_MIN_ATOMS: usize = 8192;
        let atoms = self.sat_atoms.len();
        if atoms < PHASE_EPOCH_MIN_ATOMS {
            ay_core::forgone::charge(ay_core::forgone::PHASE_EPOCH_NIA, atoms as u64);
            return None;
        }
        Some(self.lia.lra_solver().phase_state_epoch())
    }

    fn supports_theory_aware_branching(&self) -> bool {
        true
    }

    /// clauseSMT Technique 2 (#8453): arithmetic propagation branching.
    /// Prioritize atoms involving blocked variables (empty feasible set)
    /// and fixed variables (singleton feasible set).
    ///
    /// Blocked vars have no satisfying assignment -- deciding atoms involving
    /// them forces early conflict detection.
    /// Fixed vars have exactly one satisfying value -- deciding their atoms
    /// eliminates search branches.
    fn suggest_decision_atom(&self) -> Option<(TermId, bool)> {
        // Highest priority: unassigned atoms involving blocked variables
        for &blocked_var in &self.blocked_vars {
            for &atom in &self.registered_atoms {
                if self.asserted_atom_set.contains(&atom) {
                    continue; // Already decided
                }
                if let Some((free_var, fs_true)) = self.compute_literal_feasible_set(atom, true) {
                    if free_var == blocked_var {
                        // Suggest the phase that has a non-empty feasible set
                        // (or false if both are empty, to force conflict quickly)
                        return Some((atom, !fs_true.is_empty()));
                    }
                }
            }
        }

        // Second priority: unassigned atoms involving fixed variables
        for (fixed_var, ref _value) in &self.fixed_vars {
            for &atom in &self.registered_atoms {
                if self.asserted_atom_set.contains(&atom) {
                    continue; // Already decided
                }
                if let Some((free_var, fs_true)) = self.compute_literal_feasible_set(atom, true) {
                    if free_var == *fixed_var {
                        return Some((atom, !fs_true.is_empty()));
                    }
                }
            }
        }

        // Third priority: feasible-set look-ahead for narrowed variables.
        // If a registered atom involves a variable with a non-trivial feasible
        // set, suggest the phase consistent with the feasible set.
        for &atom in &self.registered_atoms {
            if self.asserted_atom_set.contains(&atom) {
                continue;
            }
            if let Some((free_var, fs_true)) = self.compute_literal_feasible_set(atom, true) {
                if let Some(fs) = self.feasible_sets.get(&free_var) {
                    if !fs.is_empty() && fs.num_intervals() < 3 {
                        // Variable has a tight feasible set -- suggest phase
                        // consistent with it.
                        let true_consistent =
                            !fs_true.is_empty() && !fs.intersection(&fs_true).is_empty();
                        if true_consistent {
                            return Some((atom, true));
                        }
                        if let Some((_fv, fs_false)) =
                            self.compute_literal_feasible_set(atom, false)
                        {
                            let false_consistent =
                                !fs_false.is_empty() && !fs.intersection(&fs_false).is_empty();
                            if false_consistent {
                                return Some((atom, false));
                            }
                        }
                    }
                }
            }
        }

        None
    }
}
