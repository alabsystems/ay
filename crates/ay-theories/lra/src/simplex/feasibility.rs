// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

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
            let error = if self.bland_mode {
                // In bland mode, use negative var index so smallest-index wins
                // (BinaryHeap is max-heap, so -var gives smallest-first ordering)
                -f64::from(var)
            } else {
                self.compute_violation_error(var)
            };
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
                let error = if self.bland_mode {
                    -f64::from(var)
                } else {
                    self.compute_violation_error(var)
                };
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
