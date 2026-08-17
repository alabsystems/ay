// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// #group-l-shortpoly: cached `--no-lra-shortest-poly` gate — DEFAULT-ON (opt out =0).
/// See `pivot_error_key`. Cheap OnceLock atomic-load in the pivot-selection hot path.
/// Adopted from OpenSMT (2025 Inc QF_LRA winner): the shortest-polynomial leaving-
/// variable rule beats AY's prior Z3/Dantzig most-violated rule on the scored
/// hybrid_networks corpus — measured +9% (@60s, 342->373; all on .bmc's wide
/// unrolling rows), 0-wrong vs z3 (216 check-sats) + 3 soundness tests. Sound by
/// construction: leaving-variable choice never changes the Farkas conflict.
fn shortest_poly_pivot_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| !ay_core::theory_disable_flags().no_lra_shortest_poly)
}

#[inline]
const fn use_shortest_poly_pivot(integer_mode: bool, enabled: bool) -> bool {
    // The heuristic was benchmarked for rational QF_LRA. LIA embeds this
    // simplex as a relaxation and relies on the historical greatest-error path
    // for stable invariant discovery; applying the LRA pivot there regresses
    // certified CHC discharge (dillig12_m #4751).
    !integer_mode && enabled
}

impl LraSolver {
    /// Check if a variable's current value violates its bounds.
    ///
    /// Uses allocation-free comparison against bound values (#6617).
    /// Previous version called `Bound::as_inf()` which clones `BigRational`
    /// (heap allocation) — this was the dominant cost in `rebuild_infeasible_heap`.
    pub(crate) fn violates_bounds(&self, var: u32) -> Option<BoundType> {
        let info = &self.vars[var as usize];
        if let Some(ref lower) = info.lower {
            if info
                .value
                .lt_bound(&lower.value, lower.strict, BoundType::Lower)
            {
                return Some(BoundType::Lower);
            }
        }
        if let Some(ref upper) = info.upper {
            if info
                .value
                .gt_bound(&upper.value, upper.strict, BoundType::Upper)
            {
                return Some(BoundType::Upper);
            }
        }
        None
    }

    /// Compute the f64 approximation of a variable's bound violation magnitude.
    /// Returns 0.0 if the variable is feasible. Used as the heap key for
    /// greatest-error pivot selection (#4919 Phase 1).
    ///
    /// Uses allocation-free bound comparison and f64 approximation (#6617).
    /// The epsilon component is infinitesimal and does not affect the f64 result.
    ///
    /// Reference: Z3 `select_greatest_error_var()` in `theory_arith_core.h:2270-2300`.
    fn compute_violation_error(&self, var: u32) -> f64 {
        let info = &self.vars[var as usize];
        // Check lower bound violation: bound - value (f64 approximation)
        if let Some(ref lower) = info.lower {
            if info
                .value
                .lt_bound(&lower.value, lower.strict, BoundType::Lower)
            {
                // error ≈ |bound.value - value.x| in f64
                let bound_f64 = lower.value_approx_f64();
                let value_f64 = info.value.x_approx_f64();
                return (bound_f64 - value_f64).abs().max(f64::MIN_POSITIVE);
            }
        }
        // Check upper bound violation: value - bound (f64 approximation)
        if let Some(ref upper) = info.upper {
            if info
                .value
                .gt_bound(&upper.value, upper.strict, BoundType::Upper)
            {
                let value_f64 = info.value.x_approx_f64();
                let bound_f64 = upper.value_approx_f64();
                return (value_f64 - bound_f64).abs().max(f64::MIN_POSITIVE);
            }
        }
        0.0
    }

    /// #group-l-shortpoly (`--no-lra-shortest-poly`): the pivot leaving-variable
    /// selection key. Default for rational LRA (ON) = OpenSMT's
    /// shortest-polynomial rule; integer-mode LIA always retains the historical
    /// Z3/Dantzig most-violated rule because this QF_LRA heuristic can perturb
    /// integer invariant discovery. `--no-lra-shortest-poly` opts rational LRA
    /// out as well.
    ///
    /// The shortest-polynomial rule:
    /// among infeasible basic vars prefer the one whose tableau ROW has the fewest
    /// terms, because pivoting on a short row substitutes into fewer/smaller rows,
    /// so each pivot is O(small). OpenSMT (the 2025 Inc QF_LRA winner) uses this as
    /// its default (getBasicVarToFixByShortestPoly). SOUND: leaving-variable choice
    /// never changes the Farkas conflict, only the pivot path — verdicts are
    /// identical, only speed differs. Max-heap semantics → negate the width so the
    /// SHORTEST row is popped first.
    #[inline]
    fn pivot_error_key(&self, var: u32) -> f64 {
        if self.bland_mode {
            // Anti-cycling: smallest var index first (negated for the max-heap).
            return -f64::from(var);
        }
        if use_shortest_poly_pivot(self.integer_mode, shortest_poly_pivot_enabled()) {
            if let Some(VarStatus::Basic(row_idx)) = self.vars[var as usize].status {
                if let Some(row) = self.rows.get(row_idx) {
                    // fewest-terms-first; tiebreak toward smaller var index for determinism
                    return -(row.coeffs.len() as f64) - f64::from(var) * 1e-9;
                }
            }
            return -f64::from(var);
        }
        self.compute_violation_error(var)
    }

    /// Update the infeasible_heap membership for a variable (#4919).
    /// If the variable is basic and violates its bounds, ensure it's in the heap
    /// with its current violation magnitude as the key.
    /// If it's basic and feasible (or non-basic), ensure it's removed.
    /// Reference: Z3 `lp_core_solver_base.h:562-582` `track_column_feasibility`.
    /// #inc-heap-epoch: logically clear the heap-membership set in O(1) by
    /// bumping the epoch; on wrap (once per 2^32 clears) re-zero the stamps.
    #[inline]
    pub(crate) fn bump_heap_epoch(&mut self) {
        self.heap_epoch = self.heap_epoch.wrapping_add(1);
        if self.heap_epoch == 0 {
            for e in self.in_infeasible_heap.iter_mut() {
                *e = 0;
            }
            self.heap_epoch = 1;
        }
    }

    pub(crate) fn track_var_feasibility(&mut self, var: u32) {
        let vi = var as usize;
        // Only track basic variables — non-basic vars are not in the heap
        if !matches!(
            self.vars.get(vi).and_then(|v| v.status.as_ref()),
            Some(VarStatus::Basic(_))
        ) {
            // If it was in the heap (e.g., just became non-basic via pivot), remove it
            if vi < self.in_infeasible_heap.len() && self.in_infeasible_heap[vi] == self.heap_epoch
            {
                self.in_infeasible_heap[vi] = 0;
                // Lazy deletion: the heap entry will be skipped when extracted
            }
            return;
        }
        let violation = self.violates_bounds(var);
        // Ensure membership bitvec is large enough
        if vi >= self.in_infeasible_heap.len() {
            self.in_infeasible_heap.resize(vi + 1, 0);
        }
        if violation.is_some() && self.in_infeasible_heap[vi] != self.heap_epoch {
            self.in_infeasible_heap[vi] = self.heap_epoch;
            let error = self.pivot_error_key(var);
            self.infeasible_heap.push(ErrorKey(error, var));
        } else if violation.is_none() && self.in_infeasible_heap[vi] == self.heap_epoch {
            self.in_infeasible_heap[vi] = 0;
            // Lazy deletion: stale entries are filtered on extraction
        }
    }

    /// Rebuild the infeasible heap from scratch (#4919).
    /// Called at the start of dual_simplex and after pop() when bounds change.
    pub(super) fn rebuild_infeasible_heap(&mut self) {
        self.infeasible_heap.clear();
        let needed = self.vars.len();
        if self.in_infeasible_heap.len() < needed {
            self.in_infeasible_heap.resize(needed, 0);
        }
        // #inc-heap-epoch: O(1) logical clear of all membership stamps.
        self.bump_heap_epoch();
        // Insert all infeasible basic variables with violation magnitude as key
        for row in &self.rows {
            let var = row.basic_var;
            if self.violates_bounds(var).is_some() {
                self.in_infeasible_heap[var as usize] = self.heap_epoch;
                let error = self.pivot_error_key(var);
                self.infeasible_heap.push(ErrorKey(error, var));
            }
        }
        self.heap_stale = false;
    }

    /// Extract the infeasible basic variable with the greatest bound violation (#4919).
    /// Returns `(row_idx, BoundType)` or `None` if no basic variable is infeasible.
    /// Uses lazy deletion: stale entries (vars that became feasible) are skipped.
    ///
    /// In bland_mode, the heap keys are negative var indices, so smallest-index
    /// is extracted first (anti-cycling guarantee).
    pub(super) fn pop_greatest_error(&mut self) -> Option<(usize, BoundType)> {
        while let Some(ErrorKey(_, var)) = self.infeasible_heap.pop() {
            let vi = var as usize;
            // Skip stale entries (lazy deletion)
            if vi >= self.in_infeasible_heap.len() || self.in_infeasible_heap[vi] != self.heap_epoch
            {
                continue;
            }
            // Verify still infeasible
            if let Some(bound_type) = self.violates_bounds(var) {
                // Found a valid infeasible basic var — look up its row
                self.in_infeasible_heap[vi] = 0;
                if let Some(VarStatus::Basic(row_idx)) = self.vars[vi].status {
                    return Some((row_idx, bound_type));
                }
                // Not basic anymore (shouldn't happen, but defensive)
            } else {
                // Was in heap but became feasible — remove membership
                self.in_infeasible_heap[vi] = 0;
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::use_shortest_poly_pivot;

    #[test]
    fn shortest_poly_is_lra_only_even_when_enabled_by_default() {
        assert!(use_shortest_poly_pivot(false, true));
        assert!(!use_shortest_poly_pivot(true, true));
        assert!(!use_shortest_poly_pivot(false, false));
        assert!(!use_shortest_poly_pivot(true, false));
    }
}
