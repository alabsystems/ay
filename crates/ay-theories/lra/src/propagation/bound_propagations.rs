// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// - If `x >= lb` and atom is `x >= k` with `lb >= k`: atom is TRUE
    /// - If `x <= ub` and atom is `x <= k` with `ub <= k`: atom is TRUE
    /// - If `x >= lb` and atom is `x <= k` with `lb > k`: atom is FALSE
    /// - If `x <= ub` and atom is `x >= k` with `ub < k`: atom is FALSE
    ///
    /// For strict bounds, the comparison is adjusted accordingly.
    ///
    /// Reference: Z3 `theory_lra.cpp:2924-2984`
    pub(crate) fn compute_bound_propagations_for_vars(&mut self, dirty_vars: &[u32]) {
        let debug = self.debug_lra;
        for &var in dirty_vars {
            self.compute_direct_bound_propagations_for_var(var);
        }

        // Phase 2: Implied-bound propagation (#4919).
        //
        // #8422: Batched per-variable reason collection.
        // Z3's propagate_lp_solver_bound() (arith_solver.cpp:230-272) collects
        // the LP explanation ONCE per implied bound, then propagates to ALL atoms
        // on that variable using the same reason. AY previously created per-atom
        // DeferredReason::ImpliedBound tokens, requiring per-atom reason
        // materialization in propagate_impl(). This caused:
        //   1. O(atoms * reason_chain) cost vs Z3's O(1 * reason_chain + atoms)
        //   2. 40-97% stale-reason filter rejections when reason collection fails
        //      on some atoms but not others (basis changes between collection
        //      attempts, BoundExplanation missing for dense-row-skipped bounds)
        //
        // New approach: for each dirty variable with implied bounds, collect
        // the upper-bound reason and lower-bound reason ONCE at the variable
        // level, then emit eager propagations with the shared reason for all
        // atoms implied by that bound. This matches Z3's architecture exactly.
        //
        // Reference: Z3's new solver (arith_solver.h) uses UINT_MAX -- never
        // disables bound propagation. This is the primary source of Z3's 228K
        // propagations vs AY's 42K on QF_LRA benchmarks.
        let mut implied_count = 0u32;
        for &var in dirty_vars {
            let vi = var as usize;
            // #7851 D2: Skip variables where all bound atoms are already assigned.
            if vi < self.unassigned_atom_count.len() && self.unassigned_atom_count[vi] == 0 {
                continue;
            }
            if vi >= self.implied_bounds.len() {
                continue;
            }
            let ub_ib_info = self.implied_bounds[vi]
                .1
                .as_ref()
                .filter(|b| b.row_idx != usize::MAX)
                .map(|b| (&b.value, b.strict, b.row_idx));
            let lb_ib_info = self.implied_bounds[vi]
                .0
                .as_ref()
                .filter(|b| b.row_idx != usize::MAX)
                .map(|b| (&b.value, b.strict, b.row_idx));

            if ub_ib_info.is_none() && lb_ib_info.is_none() {
                continue;
            }

            // #7853: Swap atoms out of atom_index instead of cloning Vec<AtomRef>.
            // Avoids per-variable heap allocation for Rational::Big bound values.
            // Placed after early-exit checks to minimize swap/swap-back overhead.
            let atoms = self
                .atom_index
                .get_mut(&var)
                .map(std::mem::take)
                .unwrap_or_default();

            // #8467/#9704: Lazy justification for implied-bound propagations.
            //
            // Instead of eagerly collecting reasons (which involves iterating
            // contributing_vars, walking BoundExplanation chains, and cloning
            // Vec<TheoryLit> per atom), emit deferred ImpliedBound propagations.
            // Reasons are materialized on demand via explain_propagation()
            // during conflict analysis (~90% never need materialization).
            //
            // Previously (#8422), reasons were batch-collected once per variable
            // and cloned per atom. The lazy approach eliminates both the collection
            // and the cloning entirely for the ~90% that are never explained.

            for atom in &atoms {
                if self.asserted.contains_key(&atom.term) {
                    continue;
                }

                if atom.is_upper {
                    // Atom: x <= k -- check implied upper bound
                    if !self.propagated_atoms.contains(&(atom.term, true)) {
                        if let Some((ub_val, ub_strict, _row_idx)) = ub_ib_info {
                            let cmp = ub_val.cmp(&atom.bound_value);
                            let implied = if atom.strict {
                                cmp == std::cmp::Ordering::Less
                                    || (cmp == std::cmp::Ordering::Equal && ub_strict)
                            } else {
                                cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                            };
                            if implied {
                                Self::note_propagated(
                                    &mut self.propagated_atoms,
                                    &mut self.propagated_trail,
                                    atom.term,
                                    true,
                                );
                                self.pending_propagations.push(PendingPropagation::deferred(
                                    TheoryLit::new(atom.term, true),
                                    DeferredReason::ImpliedBound {
                                        var,
                                        need_upper: true,
                                    },
                                ));
                                implied_count += 1;
                                continue;
                            }
                        }
                    }
                    // Atom: x <= k -- check implied lower bound for false
                    if !self.propagated_atoms.contains(&(atom.term, false)) {
                        if let Some((lb_val, lb_strict, _row_idx)) = lb_ib_info {
                            let cmp = lb_val.cmp(&atom.bound_value);
                            let implied_false = if atom.strict {
                                cmp == std::cmp::Ordering::Greater
                                    || cmp == std::cmp::Ordering::Equal
                            } else {
                                cmp == std::cmp::Ordering::Greater
                                    || (cmp == std::cmp::Ordering::Equal && lb_strict)
                            };
                            if implied_false {
                                Self::note_propagated(
                                    &mut self.propagated_atoms,
                                    &mut self.propagated_trail,
                                    atom.term,
                                    false,
                                );
                                self.pending_propagations.push(PendingPropagation::deferred(
                                    TheoryLit::new(atom.term, false),
                                    DeferredReason::ImpliedBound {
                                        var,
                                        need_upper: false,
                                    },
                                ));
                                implied_count += 1;
                            }
                        }
                    }
                } else {
                    // Atom: x >= k -- check implied lower bound for true
                    if !self.propagated_atoms.contains(&(atom.term, true)) {
                        if let Some((lb_val, lb_strict, _row_idx)) = lb_ib_info {
                            let cmp = lb_val.cmp(&atom.bound_value);
                            let implied = if atom.strict {
                                cmp == std::cmp::Ordering::Greater
                                    || (cmp == std::cmp::Ordering::Equal && lb_strict)
                            } else {
                                cmp == std::cmp::Ordering::Greater
                                    || cmp == std::cmp::Ordering::Equal
                            };
                            if implied {
                                Self::note_propagated(
                                    &mut self.propagated_atoms,
                                    &mut self.propagated_trail,
                                    atom.term,
                                    true,
                                );
                                self.pending_propagations.push(PendingPropagation::deferred(
                                    TheoryLit::new(atom.term, true),
                                    DeferredReason::ImpliedBound {
                                        var,
                                        need_upper: false,
                                    },
                                ));
                                implied_count += 1;
                                continue;
                            }
                        }
                    }
                    // Atom: x >= k -- check implied upper bound for false
                    if !self.propagated_atoms.contains(&(atom.term, false)) {
                        if let Some((ub_val, ub_strict, _row_idx)) = ub_ib_info {
                            let cmp = ub_val.cmp(&atom.bound_value);
                            let implied_false = if atom.strict {
                                cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                            } else {
                                cmp == std::cmp::Ordering::Less
                                    || (cmp == std::cmp::Ordering::Equal && ub_strict)
                            };
                            if implied_false {
                                Self::note_propagated(
                                    &mut self.propagated_atoms,
                                    &mut self.propagated_trail,
                                    atom.term,
                                    false,
                                );
                                self.pending_propagations.push(PendingPropagation::deferred(
                                    TheoryLit::new(atom.term, false),
                                    DeferredReason::ImpliedBound {
                                        var,
                                        need_upper: true,
                                    },
                                ));
                                implied_count += 1;
                            }
                        }
                    }
                }
            }
            // #7853: Swap atoms back into atom_index.
            if let Some(slot) = self.atom_index.get_mut(&var) {
                *slot = atoms;
            } else if !atoms.is_empty() {
                self.atom_index.insert(var, atoms);
            }
        }

        if debug && !self.pending_propagations.is_empty() {
            safe_eprintln!(
                "[LRA] Computed {} bound propagations ({} from implied bounds)",
                self.pending_propagations.len(),
                implied_count,
            );
        }
        if debug && !self.pending_bound_refinements.is_empty() {
            safe_eprintln!(
                "[LRA] Queued {} bound refinements",
                self.pending_bound_refinements.len(),
            );
        }
    }

    /// #8422: Collect the reason for a variable's implied bound, trying multiple
    /// strategies with fallback. Returns `Some(reason)` on success, `None` if all
    /// strategies fail.
    ///
    /// This is called ONCE per (variable, direction) pair and the result is shared
    /// across all atoms implied by that bound, matching Z3's
    /// `propagate_lp_solver_bound()` which calls `explain_implied_bound()` once.
    ///
    /// Strategy order:
    /// 1. BoundExplanation chain (collect_reasons_from_explanation) -- walks the
    ///    contributing_vars tree stored at derivation time
    /// 2. Single-row reason collection -- reads the current row directly
    /// 3. Interval-based collection -- uses expression interval with current bounds
    #[allow(dead_code)]
    fn collect_implied_bound_reason_for_var(
        &self,
        var_idx: usize,
        need_upper: bool,
    ) -> Option<Vec<TheoryLit>> {
        // Strategy 1: BoundExplanation chain (cheapest, most accurate).
        if let Some(reasons) = self.make_eager_implied_propagation_reasons(var_idx, need_upper) {
            if !reasons.is_empty()
                && reasons
                    .iter()
                    .all(|r| self.asserted.get(&r.term) == Some(&r.value))
            {
                return Some(reasons);
            }
        }

        // Strategy 2: Single-row reason collection.
        let ib = if need_upper {
            self.implied_bounds.get(var_idx).and_then(|p| p.1.as_ref())
        } else {
            self.implied_bounds.get(var_idx).and_then(|p| p.0.as_ref())
        };
        if let Some(ib) = ib {
            if ib.row_idx != usize::MAX {
                if let Some(reasons) =
                    self.collect_single_row_reasons(var_idx as u32, need_upper, ib.row_idx)
                {
                    if !reasons.is_empty()
                        && reasons
                            .iter()
                            .all(|r| self.asserted.get(&r.term) == Some(&r.value))
                    {
                        return Some(reasons);
                    }
                }
            }
        }

        // Strategy 3: Interval-based reasons from any atom on this variable.
        // This strategy works even when BoundExplanation chains are incomplete.
        if let Some(atoms) = self.atom_index.get(&(var_idx as u32)) {
            for atom in atoms {
                if let Some(Some(info)) = self.atom_cache.get(&atom.term) {
                    // #7853: Use reference instead of cloning LinearExpr.
                    // All borrows in this chain are shared (&self).
                    let reason = self.collect_interval_reasons(&info.expr, need_upper);
                    if !reason.is_empty()
                        && reason
                            .iter()
                            .all(|r| self.asserted.get(&r.term) == Some(&r.value))
                    {
                        return Some(reason);
                    }
                }
            }
        }

        None
    }
}
