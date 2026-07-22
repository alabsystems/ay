// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    pub(crate) fn assert_parsed_atom_polarity_with_reasons(
        &mut self,
        info: &ParsedAtomInfo,
        value: bool,
        reasons: &[(TermId, bool)],
    ) -> bool {
        if info.is_eq || info.is_distinct {
            return false;
        }

        // #8406: Rational::zero() avoids BigRational heap allocation.
        let zero = Rational::zero();
        if value {
            if info.is_le {
                self.assert_bound_with_reasons(
                    info.expr.clone(),
                    zero,
                    BoundType::Upper,
                    info.strict,
                    reasons,
                    None,
                );
            } else {
                self.assert_bound_with_reasons(
                    info.expr.clone(),
                    zero,
                    BoundType::Lower,
                    info.strict,
                    reasons,
                    None,
                );
            }
        } else if info.is_le {
            self.assert_bound_with_reasons(
                info.expr.clone(),
                zero,
                BoundType::Lower,
                !info.strict,
                reasons,
                None,
            );
        } else {
            self.assert_bound_with_reasons(
                info.expr.clone(),
                zero,
                BoundType::Upper,
                !info.strict,
                reasons,
                None,
            );
        }
        true
    }

    pub(crate) fn collect_model_seed_candidates(&self) -> Vec<TheoryLit> {
        const MAX_MODEL_SEED_CANDIDATES: usize = 8;

        let mut vars: Vec<u32> = self.atom_index.keys().copied().collect();
        vars.sort_unstable();

        let mut candidates = Vec::new();
        for var in vars {
            let Some(atoms) = self.atom_index.get(&var) else {
                continue;
            };
            let vi = var as usize;
            let direct_lb = self.vars.get(vi).and_then(|info| info.lower.as_ref());
            let direct_ub = self.vars.get(vi).and_then(|info| info.upper.as_ref());
            let implied_lb = self
                .implied_bounds
                .get(vi)
                .and_then(|bounds| bounds.0.as_ref());
            let implied_ub = self
                .implied_bounds
                .get(vi)
                .and_then(|bounds| bounds.1.as_ref());

            let mut best_upper: Option<&AtomRef> = None;
            let mut best_lower: Option<&AtomRef> = None;

            for atom in atoms {
                if self.asserted.contains_key(&atom.term)
                    || self.propagated_atoms.contains(&(atom.term, true))
                {
                    continue;
                }
                if self.suggest_phase(atom.term) != Some(true) {
                    continue;
                }
                if atom.is_upper {
                    if direct_ub.is_some() || implied_ub.is_some() {
                        continue;
                    }
                    let replace = match best_upper {
                        None => true,
                        Some(existing) => {
                            atom.bound_value < existing.bound_value
                                || (atom.bound_value == existing.bound_value
                                    && atom.strict
                                    && !existing.strict)
                        }
                    };
                    if replace {
                        best_upper = Some(atom);
                    }
                } else {
                    if direct_lb.is_some() || implied_lb.is_some() {
                        continue;
                    }
                    let replace = match best_lower {
                        None => true,
                        Some(existing) => {
                            atom.bound_value > existing.bound_value
                                || (atom.bound_value == existing.bound_value
                                    && atom.strict
                                    && !existing.strict)
                        }
                    };
                    if replace {
                        best_lower = Some(atom);
                    }
                }
            }

            if let Some(atom) = best_upper {
                candidates.push(TheoryLit::new(atom.term, true));
            }
            if let Some(atom) = best_lower {
                candidates.push(TheoryLit::new(atom.term, true));
            }

            if candidates.len() >= MAX_MODEL_SEED_CANDIDATES {
                break;
            }
        }

        candidates.truncate(MAX_MODEL_SEED_CANDIDATES);
        candidates
    }

    pub(crate) fn try_prove_model_seed_literal(
        &mut self,
        literal: TheoryLit,
    ) -> Option<Vec<TheoryLit>> {
        let info = self.atom_cache.get(&literal.term)?.clone()?;
        if info.is_eq || info.is_distinct {
            return None;
        }

        let sentinel_reason = [(TermId::SENTINEL, true)];
        self.push();
        if !self.assert_parsed_atom_polarity_with_reasons(&info, !literal.value, &sentinel_reason) {
            self.pop();
            return None;
        }

        let proof = match self.dual_simplex() {
            TheoryResult::Unsat(conflict) if !conflict.is_empty() => Some(conflict),
            TheoryResult::UnsatWithFarkas(conflict) if !conflict.literals.is_empty() => {
                Some(conflict.literals)
            }
            _ => None,
        };
        self.pop();
        proof
    }

    pub(crate) fn queue_model_seeded_propagations(&mut self, debug: bool) {
        if !self.last_simplex_feasible || !self.pending_propagations.is_empty() {
            return;
        }

        let candidates = self.collect_model_seed_candidates();
        if candidates.is_empty() {
            return;
        }

        let saved_pending_bound_refinements = std::mem::take(&mut self.pending_bound_refinements);
        let saved_pending_propagations = std::mem::take(&mut self.pending_propagations);
        let saved_propagated_atoms = std::mem::take(&mut self.propagated_atoms);
        let saved_propagation_dirty_vars = std::mem::take(&mut self.propagation_dirty_vars);
        let saved_implied_bounds = self.implied_bounds.clone();
        let saved_touched_rows = self.touched_rows.clone();
        let saved_propagate_direct_touched_rows_pending =
            self.propagate_direct_touched_rows_pending;
        let saved_implied_bounds_fresh = self.implied_bounds_fresh;
        let saved_pending_diseq_splits = std::mem::take(&mut self.pending_diseq_splits);
        let saved_pending_expr_splits = std::mem::take(&mut self.pending_expr_splits);
        let saved_pending_equalities = std::mem::take(&mut self.pending_equalities);
        let saved_propagated_equality_pairs = std::mem::take(&mut self.propagated_equality_pairs);
        let saved_fixed_term_value_table = self.fixed_term_value_table.clone();
        let saved_fixed_term_value_members = self.fixed_term_value_members.clone();
        let saved_pending_fixed_term_equalities = self.pending_fixed_term_equalities.clone();
        let saved_pending_offset_equalities = self.pending_offset_equalities.clone();
        let saved_trivial_conflict = self.trivial_conflict.clone();
        let saved_last_simplex_feasible = self.last_simplex_feasible;
        let saved_bounds_tightened_since_simplex = self.bounds_tightened_since_simplex;
        let saved_vars_tightened_since_simplex =
            std::mem::take(&mut self.vars_tightened_since_simplex);
        let saved_dirty = self.dirty;
        let saved_last_compound_propagations_queued = self.last_compound_propagations_queued;
        let saved_last_compound_wake_dirty_hits = self.last_compound_wake_dirty_hits;
        let saved_last_compound_wake_candidates = self.last_compound_wake_candidates;

        let attempted_any = !candidates.is_empty();
        let mut proven = Vec::new();
        for literal in candidates {
            if let Some(reason) = self.try_prove_model_seed_literal(literal) {
                proven.push(TheoryPropagation {
                    literal,
                    reason,
                    reason_data: None,
                });
            }
        }

        if attempted_any {
            // `try_prove_model_seed_literal` explores temporary opposite bounds
            // under push/pop scopes. `pop()` restores bounds but not the current
            // simplex basis/values, so rebuild a feasible model for the original
            // scope before returning to DPLL.
            let restore = self.dual_simplex();
            debug_assert!(
                matches!(restore, TheoryResult::Sat),
                "BUG: model-seeded propagation restore failed: {restore:?}"
            );
        }

        self.pending_bound_refinements = saved_pending_bound_refinements;
        self.pending_propagations = saved_pending_propagations;
        self.propagated_atoms = saved_propagated_atoms;
        self.propagation_dirty_vars = saved_propagation_dirty_vars;
        self.implied_bounds = saved_implied_bounds;
        self.touched_rows = saved_touched_rows;
        self.propagate_direct_touched_rows_pending = saved_propagate_direct_touched_rows_pending;
        self.implied_bounds_fresh = saved_implied_bounds_fresh;
        self.pending_diseq_splits = saved_pending_diseq_splits;
        self.pending_expr_splits = saved_pending_expr_splits;
        self.pending_equalities = saved_pending_equalities;
        self.propagated_equality_pairs = saved_propagated_equality_pairs;
        self.fixed_term_value_table = saved_fixed_term_value_table;
        self.fixed_term_value_members = saved_fixed_term_value_members;
        self.pending_fixed_term_equalities = saved_pending_fixed_term_equalities;
        self.pending_offset_equalities = saved_pending_offset_equalities;
        self.trivial_conflict = saved_trivial_conflict;
        self.last_simplex_feasible = saved_last_simplex_feasible;
        self.bounds_tightened_since_simplex = saved_bounds_tightened_since_simplex;
        self.vars_tightened_since_simplex = saved_vars_tightened_since_simplex;
        self.dirty = saved_dirty;
        self.last_compound_propagations_queued = saved_last_compound_propagations_queued;
        self.last_compound_wake_dirty_hits = saved_last_compound_wake_dirty_hits;
        self.last_compound_wake_candidates = saved_last_compound_wake_candidates;

        let mut seeded = 0usize;
        for propagation in proven {
            if self
                .propagated_atoms
                .insert((propagation.literal.term, propagation.literal.value))
            {
                self.pending_propagations
                    .push(PendingPropagation::eager_propagation(propagation));
                seeded += 1;
            }
        }

        if debug && seeded > 0 {
            safe_eprintln!(
                "[LRA] model-seeded propagation queued {} literal(s)",
                seeded
            );
        }
    }
}
