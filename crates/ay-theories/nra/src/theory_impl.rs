// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `NraSolver`.
//!
//! Implements the DPLL(T) theory interface for the nonlinear real arithmetic theory.

use super::*;

impl TheorySolver for NraSolver<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.last_unsat_certificate = None;
        // Undo any tentative patch before asserting new literals —
        // assertions must go into the real scope, not the patch scope.
        self.undo_tentative_patch();

        let (term, val) = match self.terms.get(literal) {
            TermData::Not(inner) => (*inner, !value),
            _ => (literal, value),
        };

        self.asserted.push((term, val));
        // Track asserted atoms for suggest_decision_atom (#8445)
        self.asserted_atom_set.insert(term);
        self.collect_nonlinear_terms(term);

        if let Some((subject, constraint)) = sign::extract_sign_constraint(self.terms, term, val) {
            if matches!(self.terms.get(subject), TermData::Var(_, _)) {
                self.sign_constraint_trail
                    .push(SignConstraintTrailEntry::Variable(subject));
            }
            if let Some(vars) = sign::record_sign_constraint(
                self.terms,
                &self.aux_to_monomial,
                &mut self.sign_constraints,
                &mut self.var_sign_constraints,
                subject,
                constraint,
                term,
            ) {
                self.sign_constraint_trail
                    .push(SignConstraintTrailEntry::Monomial(vars));
            }
        }

        self.lra.assert_literal(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count = self.check_count.saturating_add(1);
        // Clear the per-check algebraic model witnesses. They are only set
        // again if THIS check proves SAT via the exact Sturm/IVT irrational-root
        // certificate (univariate.rs). Resetting here keeps the model honest:
        // stale witnesses from a previous check must never leak into a later
        // SAT verdict's model.
        self.algebraic_model.clear();
        // Undo any stale tentative patch from a previous check —
        // the SAT solver may have backtracked or asserted new literals.
        self.undo_tentative_patch();

        // clauseSMT Technique 2 (#8445): update feasible sets for arithmetic
        // propagation branching before entering the check loop. This
        // classifies variables as blocked/fixed/narrowed to guide branching.
        self.update_feasible_sets();

        maybe_grow_nra_stack(|| self.nra_check_loop())
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let props = self.lra.propagate();
        self.propagation_count = self
            .propagation_count
            .saturating_add(u64::try_from(props.len()).unwrap_or(u64::MAX));
        props
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        let mut stats = vec![
            ("nra_checks", self.check_count),
            ("nra_conflicts", self.conflict_count),
            ("nra_propagations", self.propagation_count),
            ("nra_tangent_lemmas", self.tangent_lemma_count),
            ("nra_patches", self.patch_count),
            ("nra_sign_cuts", self.sign_cut_count),
            ("nra_feasible_set_computations", self.feasible_set_count),
            ("nra_blocked_vars", self.blocked_vars.len() as u64),
            ("nra_fixed_vars", self.fixed_vars.len() as u64),
            ("nra_icp_calls", self.icp_call_count.get()),
            ("nra_icp_main_boxes", self.icp_main_box_count.get()),
            ("nra_icp_pin_boxes", self.icp_pin_box_count.get()),
            ("nra_icp_wide_tree_caps", self.icp_wide_tree_cap_count.get()),
        ];
        stats.extend(self.lra.collect_statistics());
        stats
    }

    fn push(&mut self) {
        self.last_unsat_certificate = None;
        // Undo tentative patch scope before creating a new real scope
        self.undo_tentative_patch();
        self.scopes.push((
            self.asserted.len(),
            self.div_purifications.len(),
            self.div_terms.len(),
        ));
        // Save sign constraint trail mark for efficient pop (#8626).
        self.sign_constraint_trail_marks
            .push(self.sign_constraint_trail.len());
        self.lra.push();
        // Reset feasible sets on push — they are recomputed on each check()
        self.reset_feasible_sets();
    }

    fn pop(&mut self) {
        self.last_unsat_certificate = None;
        // Undo tentative patch scope before popping the real scope
        self.undo_tentative_patch();
        if let Some((assert_mark, div_mark, div_terms_mark)) = self.scopes.pop() {
            self.asserted.truncate(assert_mark);
            self.div_purifications.truncate(div_mark);
            self.div_terms.truncate(div_terms_mark);
            // Rebuild asserted_atom_set from the truncated asserted list (#8445)
            self.asserted_atom_set.clear();
            for &(atom, _) in &self.asserted {
                self.asserted_atom_set.insert(atom);
            }
        }
        // Undo sign constraint additions from the popped scope (#8626).
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
        self.lra.pop();
        // Reset feasible sets on pop — stale sets from the previous level
        // would include constraints that have been retracted.
        self.reset_feasible_sets();
    }

    fn reset(&mut self) {
        self.monomials.clear();
        self.scaled_aliases.clear();
        self.aux_to_monomial.clear();
        self.compound_factors.clear();
        self.compound_defs_emitted.clear();
        // The cache describes rows live in `lra`; `lra.reset()` below removes
        // every such row, so retaining a key would suppress a required row in
        // the next independent solve.
        self.linearization_rows.clear();
        self.sign_constraints.clear();
        self.var_sign_constraints.clear();
        self.sign_constraint_trail.clear();
        self.sign_constraint_trail_marks.clear();
        self.div_purifications.clear();
        self.div_terms.clear();
        self.asserted.clear();
        self.scopes.clear();
        self.tentative_depth = 0;
        self.reset_feasible_sets();
        self.fixed_factor_values.clear();
        self.fixed_lin_emitted.clear();
        self.registered_atoms.clear();
        self.asserted_atom_set.clear();
        self.sat_atoms.clear();
        self.algebraic_model.clear();
        self.last_unsat_certificate = None;
        self.lra.reset();
    }

    fn supports_farkas_semantic_check(&self) -> bool {
        self.lra.supports_farkas_semantic_check()
    }

    fn propagate_equalities(&mut self) -> ay_core::EqualityPropagationResult {
        self.lra.propagate_equalities()
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.last_unsat_certificate = None;
        self.lra.assert_shared_equality(lhs, rhs, reason);
    }

    fn assert_shared_disequality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.last_unsat_certificate = None;
        self.lra.assert_shared_disequality(lhs, rhs, reason);
    }

    fn internalize_atom(&mut self, term: TermId) {
        self.lra.internalize_atom(term);
        // clauseSMT (#8445): track all registered atoms for suggest_decision_atom.
        // This lets us find unassigned atoms involving blocked/fixed variables.
        self.registered_atoms.push(term);
        // Pre-scan for nonlinear terms so feasible-set analysis can extract
        // linear univariate forms from atoms before they are asserted.
        self.collect_nonlinear_terms(term);
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        // clauseSMT Technique 2 (#8445): use feasible-set information to
        // suggest phases that are consistent with arithmetic feasibility.
        // If we can compute a feasible set for this atom, suggest the phase
        // that keeps the feasible set non-empty.
        //
        // #nonlinear-phase-hints: `feasible_set_phase` is the allocation-free,
        // value-exact form of that decision (its doc carries the derivation);
        // the previous two-feasible-set body is `feasible_set_phase_reference`
        // and every debug build checks the two agree on every call.
        let phase = self.feasible_set_phase(atom);
        debug_assert_eq!(
            phase,
            self.feasible_set_phase_reference(atom),
            "feasible_set_phase diverged from its reference on atom {atom:?}"
        );
        if phase.is_some() {
            return phase;
        }
        self.lra.suggest_phase(atom)
    }

    fn register_atom(&mut self, atom: TermId) {
        // Count the SAT-visible vocabulary for the phase-epoch gate
        // (#nonlinear-phase-hints). Nothing else changes: the atom is still
        // parsed by the wrapped solver only when it is first asserted.
        self.sat_atoms.insert(atom);
    }

    fn phase_hint_epoch(&self) -> Option<u64> {
        // `suggest_phase` above is a function of the immutable term store and
        // of what the wrapped LRA's LRA exposes — `has_value` / `value_sign`
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
            ay_core::forgone::charge(ay_core::forgone::PHASE_EPOCH_NRA, atoms as u64);
            return None;
        }
        Some(self.lra.phase_state_epoch())
    }

    fn supports_theory_aware_branching(&self) -> bool {
        // NRA is an arithmetic theory — theory atoms should be decided before
        // Tseitin encoding variables. Additionally, the clauseSMT feasible-set
        // look-ahead (#8445) provides high-quality phase suggestions for
        // nonlinear constraints that VSIDS alone cannot discover.
        true
    }

    fn suggest_decision_atom(&self) -> Option<(TermId, bool)> {
        // clauseSMT Technique 2 (#8445): arithmetic propagation branching.
        // Prioritize atoms involving blocked variables (empty feasible set)
        // and fixed variables (singleton feasible set).
        //
        // Blocked vars have no satisfying assignment — deciding atoms involving
        // them forces early conflict detection.
        // Fixed vars have exactly one satisfying value — deciding their atoms
        // eliminates search branches.
        //
        // We search *registered* (internalized) atoms that are NOT yet asserted.
        // Already-asserted atoms have truth values and cannot be decided again.
        // The DPLL extension verifies the atom is unassigned in the SAT solver
        // before using the suggestion, but filtering here avoids wasted
        // feasible-set computation.

        // One materialisation delta for every feasible-set evaluation
        // below: this suggestion pass is read-only over one LRA model.
        let mut delta = None;

        // Highest priority: unassigned atoms involving blocked variables
        for &blocked_var in &self.blocked_vars {
            for &atom in &self.registered_atoms {
                if self.asserted_atom_set.contains(&atom) {
                    continue; // Already decided
                }
                if let Some((free_var, fs_true)) =
                    self.compute_literal_feasible_set_with_delta(atom, true, &mut delta)
                {
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
                if let Some((free_var, fs_true)) =
                    self.compute_literal_feasible_set_with_delta(atom, true, &mut delta)
                {
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
            if let Some((free_var, fs_true)) =
                self.compute_literal_feasible_set_with_delta(atom, true, &mut delta)
            {
                if let Some(fs) = self.feasible_sets.get(&free_var) {
                    if !fs.is_empty() && fs.num_intervals() < 3 {
                        // Variable has a tight feasible set — suggest phase
                        // consistent with it.
                        let true_consistent =
                            !fs_true.is_empty() && !fs.intersection(&fs_true).is_empty();
                        if true_consistent {
                            return Some((atom, true));
                        }
                        if let Some((_fv, fs_false)) =
                            self.compute_literal_feasible_set_with_delta(atom, false, &mut delta)
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
