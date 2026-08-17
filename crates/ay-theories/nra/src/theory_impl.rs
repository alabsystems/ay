// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `NraSolver`.
//!
//! Implements the DPLL(T) theory interface for the nonlinear real arithmetic theory.

use super::*;

impl TheorySolver for NraSolver<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
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
        self.check_count += 1;
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
        self.propagation_count += props.len() as u64;
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
        ];
        stats.extend(self.lra.collect_statistics());
        stats
    }

    fn push(&mut self) {
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
        self.algebraic_model.clear();
        self.lra.reset();
    }

    fn supports_farkas_semantic_check(&self) -> bool {
        self.lra.supports_farkas_semantic_check()
    }

    fn propagate_equalities(&mut self) -> ay_core::EqualityPropagationResult {
        self.lra.propagate_equalities()
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.lra.assert_shared_equality(lhs, rhs, reason);
    }

    fn assert_shared_disequality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
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
        if let Some((_free_var, fs_true)) = self.compute_literal_feasible_set(atom, true) {
            if let Some((_free_var, fs_false)) = self.compute_literal_feasible_set(atom, false) {
                // Prefer the phase that produces a non-empty feasible set
                let true_empty = fs_true.is_empty();
                let false_empty = fs_false.is_empty();
                if true_empty && !false_empty {
                    return Some(false);
                }
                if false_empty && !true_empty {
                    return Some(true);
                }
                // If both are non-empty, prefer the one with a wider feasible set
                // (more intervals = more flexibility). Fall through to LRA otherwise.
                if fs_true.num_intervals() > fs_false.num_intervals() {
                    return Some(true);
                }
                if fs_false.num_intervals() > fs_true.num_intervals() {
                    return Some(false);
                }
            }
        }
        self.lra.suggest_phase(atom)
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
                        // Variable has a tight feasible set — suggest phase
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
