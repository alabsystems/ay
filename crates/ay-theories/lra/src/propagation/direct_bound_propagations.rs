// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// #8422: Effective bound source — tracks whether the tightest bound for
/// a variable is from a direct assertion or an implied (LP-derived) bound.
/// Used to select the correct deferred reason type.
enum BoundSource {
    /// Direct bound from an assertion (row_idx == usize::MAX).
    Direct,
    /// Implied bound from LP row analysis (row_idx != usize::MAX).
    Implied,
}

impl LraSolver {
    /// #8422: Compute the effective upper bound for a variable as the tighter
    /// of direct and implied bounds. Returns (value, strict, source) or None.
    ///
    /// Z3's `propagate_lp_solver_bound` uses `get_bound(v)` which returns the
    /// tighter of the direct assertion and LP-derived bound. AY previously used
    /// `if direct { ... } else if implied { ... }` which ONLY checked implied
    /// bounds when direct bounds were absent. This missed propagations where
    /// the implied bound was tighter than the direct bound.
    ///
    /// Example: direct UB x <= 100, implied UB x <= 3, atom x <= 5.
    /// Old code: check 100 <= 5? No. Skip implied. Atom NOT propagated.
    /// New code: effective UB = min(100, 3) = 3. Check 3 <= 5? Yes. Propagated.
    fn effective_upper_bound<'a>(
        ub_direct: Option<&'a Bound>,
        ub_implied: Option<&'a ImpliedBound>,
    ) -> Option<(&'a Rational, bool, BoundSource)> {
        match (ub_direct, ub_implied) {
            (Some(d), Some(ib)) => {
                // Tighter upper bound = smaller value. On tie, prefer strict.
                let ib_tighter =
                    ib.value < d.value || (ib.value == d.value && ib.strict && !d.strict);
                if ib_tighter {
                    Some((&ib.value, ib.strict, BoundSource::Implied))
                } else {
                    Some((&d.value, d.strict, BoundSource::Direct))
                }
            }
            (Some(d), None) => Some((&d.value, d.strict, BoundSource::Direct)),
            (None, Some(ib)) => Some((&ib.value, ib.strict, BoundSource::Implied)),
            (None, None) => None,
        }
    }

    /// #8422: Compute the effective lower bound for a variable as the tighter
    /// of direct and implied bounds. Returns (value, strict, source) or None.
    fn effective_lower_bound<'a>(
        lb_direct: Option<&'a Bound>,
        lb_implied: Option<&'a ImpliedBound>,
    ) -> Option<(&'a Rational, bool, BoundSource)> {
        match (lb_direct, lb_implied) {
            (Some(d), Some(ib)) => {
                // Tighter lower bound = larger value. On tie, prefer strict.
                let ib_tighter =
                    ib.value > d.value || (ib.value == d.value && ib.strict && !d.strict);
                if ib_tighter {
                    Some((&ib.value, ib.strict, BoundSource::Implied))
                } else {
                    Some((&d.value, d.strict, BoundSource::Direct))
                }
            }
            (Some(d), None) => Some((&d.value, d.strict, BoundSource::Direct)),
            (None, Some(ib)) => Some((&ib.value, ib.strict, BoundSource::Implied)),
            (None, None) => None,
        }
    }

    pub(crate) fn compute_direct_bound_propagations_for_var(&mut self, var: u32) {
        // #7851 D2: Skip variables where all bound atoms are already assigned.
        // Matches Z3's m_unassigned_bounds[v]==0 early exit (arith_solver.cpp:149).
        let vi_check = var as usize;
        if vi_check < self.unassigned_atom_count.len() && self.unassigned_atom_count[vi_check] == 0
        {
            return;
        }
        // #7853: Swap atom refs out of atom_index instead of cloning the Vec.
        // This avoids per-dirty-var heap allocation for the common case where
        // Rational::Big values are in bound_value. The Vec is swapped back
        // after iteration completes.
        let Some(atoms) = self.atom_index.get_mut(&var).map(std::mem::take) else {
            return;
        };
        // #6564: For slack variables, reconstruct reasons from the
        // original expression instead of direct bound reason_pairs().
        let vi = var as usize;
        let Some(info) = self.vars.get(vi) else {
            return;
        };
        let is_slack = self.slack_var_set.contains(&var);

        // #8422: Use the TIGHTER of direct and implied bounds for propagation.
        //
        // Z3's propagate_lp_solver_bound (arith_solver.cpp:230-272) uses
        // get_bound(v) which returns the tighter of direct and LP-derived bounds.
        // AY previously used if/else-if cascading: check direct first, only fall
        // back to implied when direct is absent. This missed propagations where
        // the implied bound was tighter than the direct bound.
        //
        // Example: direct UB x <= 100, implied UB x <= 3, atom x <= 5.
        // Old: check direct 100 <= 5? No. Skip (implied not checked). MISSED.
        // New: effective UB = min(100, 3) = 3. Check 3 <= 5? Yes. PROPAGATED.
        //
        // This is the primary source of Z3's 228K vs AY's 42K propagation gap
        // on QF_LRA benchmarks.
        let ub_direct = info.upper.as_ref();
        let lb_direct = info.lower.as_ref();

        let ub_implied: Option<&ImpliedBound> = if vi < self.implied_bounds.len() {
            self.implied_bounds[vi]
                .1
                .as_ref()
                .filter(|b| b.row_idx != usize::MAX)
        } else {
            None
        };
        let lb_implied: Option<&ImpliedBound> = if vi < self.implied_bounds.len() {
            self.implied_bounds[vi]
                .0
                .as_ref()
                .filter(|b| b.row_idx != usize::MAX)
        } else {
            None
        };

        // #8422: Compute effective bounds (tighter of direct + implied).
        let eff_ub = Self::effective_upper_bound(ub_direct, ub_implied);
        let eff_lb = Self::effective_lower_bound(lb_direct, lb_implied);

        for atom in &atoms {
            if self.asserted.contains_key(&atom.term) {
                continue;
            }

            if atom.is_upper {
                // Atom: x <= k (or x < k if strict)
                // TRUE if effective_ub(x) satisfies atom.
                if !self.propagated_atoms.contains(&(atom.term, true)) {
                    if let Some((ub_val, ub_strict, ref source)) = eff_ub {
                        let implied_true = if atom.strict {
                            *ub_val < atom.bound_value || (*ub_val == atom.bound_value && ub_strict)
                        } else {
                            *ub_val <= atom.bound_value
                        };
                        if implied_true {
                            Self::note_propagated(
                                &mut self.propagated_atoms,
                                &mut self.propagated_trail,
                                atom.term,
                                true,
                            );
                            match source {
                                BoundSource::Implied => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, true),
                                        DeferredReason::ImpliedBound {
                                            var,
                                            need_upper: true,
                                        },
                                    ));
                                }
                                BoundSource::Direct if is_slack => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, true),
                                        DeferredReason::Interval {
                                            atom_term: atom.term,
                                            for_upper: true,
                                        },
                                    ));
                                }
                                BoundSource::Direct => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, true),
                                        DeferredReason::DirectBound {
                                            var,
                                            need_upper: true,
                                        },
                                    ));
                                }
                            }
                            continue;
                        }
                    }
                }

                // FALSE if effective_lb(x) contradicts atom.
                // For strict atom x < k: FALSE if lb >= k.
                // For non-strict x <= k: FALSE if lb > k, or lb == k and strict.
                if !self.propagated_atoms.contains(&(atom.term, false)) {
                    if let Some((lb_val, lb_strict, ref source)) = eff_lb {
                        let implied_false = if atom.strict {
                            *lb_val >= atom.bound_value
                        } else {
                            *lb_val > atom.bound_value || (*lb_val == atom.bound_value && lb_strict)
                        };
                        if implied_false {
                            Self::note_propagated(
                                &mut self.propagated_atoms,
                                &mut self.propagated_trail,
                                atom.term,
                                false,
                            );
                            match source {
                                BoundSource::Implied => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, false),
                                        DeferredReason::ImpliedBound {
                                            var,
                                            need_upper: false,
                                        },
                                    ));
                                }
                                BoundSource::Direct if is_slack => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, false),
                                        DeferredReason::Interval {
                                            atom_term: atom.term,
                                            for_upper: false,
                                        },
                                    ));
                                }
                                BoundSource::Direct => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, false),
                                        DeferredReason::DirectBound {
                                            var,
                                            need_upper: false,
                                        },
                                    ));
                                }
                            }
                        }
                    }
                }
            } else {
                // Atom: x >= k (or x > k if strict)
                // TRUE if effective_lb(x) satisfies atom.
                if !self.propagated_atoms.contains(&(atom.term, true)) {
                    if let Some((lb_val, lb_strict, ref source)) = eff_lb {
                        let implied_true = if atom.strict {
                            *lb_val > atom.bound_value || (*lb_val == atom.bound_value && lb_strict)
                        } else {
                            *lb_val >= atom.bound_value
                        };
                        if implied_true {
                            Self::note_propagated(
                                &mut self.propagated_atoms,
                                &mut self.propagated_trail,
                                atom.term,
                                true,
                            );
                            match source {
                                BoundSource::Implied => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, true),
                                        DeferredReason::ImpliedBound {
                                            var,
                                            need_upper: false,
                                        },
                                    ));
                                }
                                BoundSource::Direct if is_slack => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, true),
                                        DeferredReason::Interval {
                                            atom_term: atom.term,
                                            for_upper: false,
                                        },
                                    ));
                                }
                                BoundSource::Direct => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, true),
                                        DeferredReason::DirectBound {
                                            var,
                                            need_upper: false,
                                        },
                                    ));
                                }
                            }
                            continue;
                        }
                    }
                }

                // FALSE if effective_ub(x) contradicts atom.
                // For strict atom x > k: FALSE if ub <= k.
                // For non-strict x >= k: FALSE if ub < k, or ub == k and strict.
                if !self.propagated_atoms.contains(&(atom.term, false)) {
                    if let Some((ub_val, ub_strict, ref source)) = eff_ub {
                        let implied_false = if atom.strict {
                            *ub_val <= atom.bound_value
                        } else {
                            *ub_val < atom.bound_value || (*ub_val == atom.bound_value && ub_strict)
                        };
                        if implied_false {
                            Self::note_propagated(
                                &mut self.propagated_atoms,
                                &mut self.propagated_trail,
                                atom.term,
                                false,
                            );
                            match source {
                                BoundSource::Implied => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, false),
                                        DeferredReason::ImpliedBound {
                                            var,
                                            need_upper: true,
                                        },
                                    ));
                                }
                                BoundSource::Direct if is_slack => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, false),
                                        DeferredReason::Interval {
                                            atom_term: atom.term,
                                            for_upper: true,
                                        },
                                    ));
                                }
                                BoundSource::Direct => {
                                    self.pending_propagations.push(PendingPropagation::deferred(
                                        TheoryLit::new(atom.term, false),
                                        DeferredReason::DirectBound {
                                            var,
                                            need_upper: true,
                                        },
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
        // #7853: Swap the atoms back into atom_index to preserve the data structure.
        if let Some(slot) = self.atom_index.get_mut(&var) {
            *slot = atoms;
        } else {
            self.atom_index.insert(var, atoms);
        }
    }
}
