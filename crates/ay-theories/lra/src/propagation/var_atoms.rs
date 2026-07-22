// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// For each variable with indexed atoms, check if the current bounds
    /// imply the truth value of any unasserted atom.
    ///
    /// Same-variable chain propagation (Z3 Component 3):
    /// Eager per-variable bound propagation (#4919 RC2).
    ///
    /// Called immediately when a bound on `var` is tightened. Scans
    /// `atom_index[var]` for single-variable atoms that are now implied by
    /// the new bound, and adds them to `pending_propagations`. This gives
    /// the SAT solver immediate feedback without waiting for the full
    /// simplex round.
    ///
    /// For slack variables, reasons are constructed directly from the bound's
    /// `reason_pairs()` instead of calling `collect_slack_interval_reasons_for_var`
    /// which triggers expensive recursive row-walking (`collect_row_reasons_recursive`,
    /// measured at 15.8% of total solver time). The direct bound reason is sound:
    /// if the slack variable's bound implies the atom, the bound's own reason chain
    /// justifies it. The interval-based reconstruction in propagate() provides
    /// more precise reasons when needed for compound atoms.
    ///
    /// Reference: Z3 `theory_lra.cpp:2924-2984` (eager bound propagation).
    pub(crate) fn propagate_var_atoms(&mut self, var: u32) {
        // #8352: Lazy JIT compilation on first propagation call.
        // Compiles per-variable atom bound checks using i64/i128 cross-multiply
        // and native machine code (aarch64/x86_64) when possible.
        if !self.theory_prop_jit_compiled {
            self.compile_theory_propagation_jit();
        }

        // #8352: Try JIT fast path (native machine code or interpreted i128).
        // If all atoms for this variable are handled by the JIT, skip the
        // BigRational fallback path entirely.
        if self.try_jit_propagate_var_atoms(var) {
            return;
        }

        let atoms = match self.atom_index.get(&var).cloned() {
            Some(a) if !a.is_empty() => a,
            _ => return,
        };
        let vi = var as usize;
        let Some(info) = self.vars.get(vi) else {
            return;
        };

        let ub_direct = info.upper.as_ref();
        let lb_direct = info.lower.as_ref();

        // #8467: Lazy justification for direct-bound propagations.
        // Instead of eagerly collecting Vec<TheoryLit> reasons here (which
        // allocates + clones for EVERY propagation), use DeferredReason::DirectBound.
        // Reasons are materialized later in propagate_impl() only for propagations
        // that survive the stale-reason filter (~10% of all propagations).
        //
        // This eliminates O(reason_len) allocation per propagation in the hot path.
        // Previously (#8064), eager collection was needed to avoid stale reasons
        // when bounds were backtracked between check() and propagate(). But
        // propagate_var_atoms is called from assert_literal() during the same
        // BCP cycle, so bounds are still fresh at propagate_impl() drain time.
        // The DeferredReason::DirectBound path in propagate_impl() reads
        // vars[var].upper/lower.reason_pairs() which is sound here.
        //
        // Reference: Z3 u_dependency — stores row index, materializes on demand.
        let has_ub = ub_direct.is_some();
        let has_lb = lb_direct.is_some();

        for atom in atoms {
            if self.asserted.contains_key(&atom.term) {
                continue;
            }

            if atom.is_upper {
                // Atom: x <= k (or x < k if strict)
                // TRUE if ub(x) satisfies atom
                let implied_true = if let Some(ub) = ub_direct {
                    if atom.strict {
                        ub.value < atom.bound_value || (ub.value == atom.bound_value && ub.strict)
                    } else {
                        ub.value <= atom.bound_value
                    }
                } else {
                    false
                };

                if implied_true && !self.propagated_atoms.contains(&(atom.term, true)) && has_ub {
                    Self::note_propagated(
                        &mut self.propagated_atoms,
                        &mut self.propagated_trail,
                        atom.term,
                        true,
                    );
                    self.pending_propagations.push(PendingPropagation::deferred(
                        TheoryLit::new(atom.term, true),
                        DeferredReason::DirectBound {
                            var,
                            need_upper: true,
                        },
                    ));
                    continue;
                }

                // FALSE if lb(x) contradicts atom.
                // For strict atom x < k: lb >= k contradicts (regardless of lb strictness,
                // since both x >= k and x > k imply NOT x < k). (#6130)
                // For non-strict atom x <= k: lb > k, or lb == k with lb strict (x > k).
                let implied_false = if let Some(lb) = lb_direct {
                    if atom.strict {
                        lb.value >= atom.bound_value
                    } else {
                        lb.value > atom.bound_value || (lb.value == atom.bound_value && lb.strict)
                    }
                } else {
                    false
                };

                if implied_false && !self.propagated_atoms.contains(&(atom.term, false)) && has_lb {
                    Self::note_propagated(
                        &mut self.propagated_atoms,
                        &mut self.propagated_trail,
                        atom.term,
                        false,
                    );
                    self.pending_propagations.push(PendingPropagation::deferred(
                        TheoryLit::new(atom.term, false),
                        DeferredReason::DirectBound {
                            var,
                            need_upper: false,
                        },
                    ));
                }
            } else {
                // Atom: x >= k (or x > k if strict)
                // TRUE if lb(x) satisfies atom
                let implied_true = if let Some(lb) = lb_direct {
                    if atom.strict {
                        lb.value > atom.bound_value || (lb.value == atom.bound_value && lb.strict)
                    } else {
                        lb.value >= atom.bound_value
                    }
                } else {
                    false
                };

                if implied_true && !self.propagated_atoms.contains(&(atom.term, true)) && has_lb {
                    Self::note_propagated(
                        &mut self.propagated_atoms,
                        &mut self.propagated_trail,
                        atom.term,
                        true,
                    );
                    self.pending_propagations.push(PendingPropagation::deferred(
                        TheoryLit::new(atom.term, true),
                        DeferredReason::DirectBound {
                            var,
                            need_upper: false,
                        },
                    ));
                    continue;
                }

                // FALSE if ub(x) contradicts atom.
                // For strict atom x > k: ub <= k contradicts (regardless of ub strictness,
                // since both x <= k and x < k imply NOT x > k). (#6130)
                // For non-strict atom x >= k: ub < k, or ub == k with ub strict (x < k).
                let implied_false = if let Some(ub) = ub_direct {
                    if atom.strict {
                        ub.value <= atom.bound_value
                    } else {
                        ub.value < atom.bound_value || (ub.value == atom.bound_value && ub.strict)
                    }
                } else {
                    false
                };

                if implied_false && !self.propagated_atoms.contains(&(atom.term, false)) && has_ub {
                    Self::note_propagated(
                        &mut self.propagated_atoms,
                        &mut self.propagated_trail,
                        atom.term,
                        false,
                    );
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
