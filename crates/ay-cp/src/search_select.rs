// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable selection strategies for CP-SAT search.
//!
//! Extracted from `search.rs` to separate variable-selection heuristics
//! from search state management.

use crate::encoder::IntegerEncoder;
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;
use ay_sat::SolverContext;

use super::{SearchState, SearchStrategy};

impl SearchState {
    /// Select the best variable to branch on, according to the current strategy.
    ///
    /// Returns the selected variable, or None if all variables are fixed.
    /// For Activity and DomWDeg strategies, uses the priority heap for O(log n)
    /// selection instead of O(n) linear scans (#5812).
    pub(crate) fn select_variable(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        ctx: &dyn SolverContext,
    ) -> Option<IntVarId> {
        match self.strategy {
            SearchStrategy::FirstFail => self.select_first_fail(trail, encoder, ctx),
            SearchStrategy::DomWDeg => self.select_dom_wdeg(trail, encoder, ctx),
            SearchStrategy::Activity => self.select_activity_heap(trail, encoder, ctx),
            SearchStrategy::InputOrder => self.select_input_order(trail, encoder, ctx),
        }
    }

    /// First-fail: variable with smallest domain size.
    /// Prioritizes `search_vars` (FlatZinc annotation) when available,
    /// falling back to all variables only if every search var is fixed.
    fn select_first_fail(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        ctx: &dyn SolverContext,
    ) -> Option<IntVarId> {
        let mut best_var: Option<IntVarId> = None;
        let mut best_size = i64::MAX;

        // Try search_vars first when available
        if !self.search_vars.is_empty() {
            for &var in &self.search_vars {
                let lb = trail.lb(var);
                let ub = trail.ub(var);
                let size = ub - lb + 1;
                if size <= 1 {
                    continue;
                }
                if size < best_size {
                    if let Some(ge_lit) = encoder.lookup_ge(var, lb + 1) {
                        if ctx.value(ge_lit.variable()).is_none() {
                            best_size = size;
                            best_var = Some(var);
                        }
                    }
                }
            }
            if best_var.is_some() {
                return best_var;
            }
        }

        // Fallback: all variables (no annotation, or all search vars fixed)
        for var_idx in 0..trail.num_vars() {
            let var = IntVarId(var_idx as u32);
            let lb = trail.lb(var);
            let ub = trail.ub(var);
            let size = ub - lb + 1;

            if size <= 1 {
                continue;
            }

            if size < best_size {
                if let Some(ge_lit) = encoder.lookup_ge(var, lb + 1) {
                    if ctx.value(ge_lit.variable()).is_none() {
                        best_size = size;
                        best_var = Some(var);
                    }
                }
            }
        }

        best_var
    }

    /// Dom/wdeg: variable minimizing domain_size / weighted_degree.
    ///
    /// Uses `cached_wdeg` for O(1) per-variable wdeg lookup (instead of
    /// O(degree) recomputation). Prioritizes `search_vars` first; falls
    /// back to heap-based selection over all variables with early termination.
    fn select_dom_wdeg(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        ctx: &dyn SolverContext,
    ) -> Option<IntVarId> {
        // Try search_vars first (usually small — linear scan is fine)
        if !self.search_vars.is_empty() {
            let mut best_var: Option<IntVarId> = None;
            let mut best_ratio = f64::MAX;
            for &var in &self.search_vars {
                let lb = trail.lb(var);
                let ub = trail.ub(var);
                let size = ub - lb + 1;
                if size <= 1 {
                    continue;
                }
                if let Some(ge_lit) = encoder.lookup_ge(var, lb + 1) {
                    if ctx.value(ge_lit.variable()).is_none() {
                        let wdeg = self.cached_wdeg[var.0 as usize];
                        let ratio = size as f64 / wdeg;
                        if ratio < best_ratio {
                            best_ratio = ratio;
                            best_var = Some(var);
                        }
                    }
                }
            }
            if best_var.is_some() {
                return best_var;
            }
        }

        // Fallback: heap-based selection over all variables.
        // The heap is keyed by cached_wdeg (highest-wdeg variables first).
        // High-wdeg vars tend to have the smallest dom/wdeg ratio, so the
        // first few pops often find the best candidate. Early termination
        // stops once remaining max wdeg can't improve the current best.
        self.select_dom_wdeg_heap(trail, encoder, ctx)
    }

    /// Heap-based dom/wdeg variable selection with early termination.
    ///
    /// Pops variables in decreasing wdeg order. For each candidate, computes
    /// the actual ratio dom_size / wdeg. Terminates early when the remaining
    /// heap's max wdeg guarantees no improvement: for any remaining variable v,
    /// ratio(v) >= 2 / max_remaining_wdeg (since min unfixed domain = 2).
    fn select_dom_wdeg_heap(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        ctx: &dyn SolverContext,
    ) -> Option<IntVarId> {
        if self.heap_stale.get() {
            self.rebuild_heap();
        }

        let scores = &self.cached_wdeg;
        let mut heap = self.var_heap.borrow_mut();
        let mut reinsert = self.ws_reinsert.borrow_mut();
        reinsert.clear();
        let mut best_var: Option<IntVarId> = None;
        let mut best_ratio = f64::MAX;

        while let Some(var_idx) = heap.pop(scores) {
            let var = IntVarId(var_idx);
            let lb = trail.lb(var);
            let ub = trail.ub(var);
            let size = ub - lb + 1;

            if size <= 1 {
                // Fixed — don't re-insert (re-added on backtrack rebuild)
                continue;
            }

            // Verify decision literal is available
            let available = match encoder.lookup_ge(var, lb + 1) {
                Some(lit) => ctx.value(lit.variable()).is_none(),
                None => false,
            };
            if !available {
                reinsert.push(var_idx);
                continue;
            }

            let wdeg = scores[var_idx as usize];
            let ratio = size as f64 / wdeg;

            if ratio < best_ratio {
                if let Some(prev) = best_var {
                    reinsert.push(prev.0);
                }
                best_ratio = ratio;
                best_var = Some(var);
            } else {
                reinsert.push(var_idx);
            }

            // Early termination: for any remaining var v in the heap,
            // ratio(v) = dom(v)/wdeg(v) >= 2/wdeg(v) >= 2/peek_wdeg.
            // If 2/peek_wdeg >= best_ratio, no remaining var can improve.
            if best_var.is_some() {
                match heap.peek() {
                    Some(next_var) => {
                        let next_wdeg = scores[next_var as usize];
                        if next_wdeg <= 2.0 / best_ratio {
                            break;
                        }
                    }
                    None => break,
                }
            }
        }

        // Re-insert non-selected, unfixed variables
        for &var_idx in reinsert.iter() {
            heap.insert(var_idx, scores);
        }

        best_var
    }

    /// Activity-based: variable with highest activity score (#5812).
    ///
    /// Uses a priority heap for O(log n) extraction. Pops candidates from the
    /// heap, skipping fixed variables and those without available decision
    /// literals. Skipped variables are collected and re-inserted after
    /// selection to maintain the heap for future calls.
    fn select_activity_heap(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        ctx: &dyn SolverContext,
    ) -> Option<IntVarId> {
        if self.heap_stale.get() {
            self.rebuild_heap();
        }

        let mut heap = self.var_heap.borrow_mut();
        let mut reinsert = self.ws_reinsert.borrow_mut();
        reinsert.clear();
        let result = loop {
            let var_idx = match heap.pop(&self.var_activity) {
                Some(v) => v,
                None => break None,
            };
            let var = IntVarId(var_idx);
            let lb = trail.lb(var);
            let ub = trail.ub(var);

            if ub - lb < 1 {
                // Fixed variable — don't re-insert (will be re-added on backtrack)
                continue;
            }

            // Verify the decision literal is available
            if let Some(ge_lit) = encoder.lookup_ge(var, lb + 1) {
                if ctx.value(ge_lit.variable()).is_some() {
                    reinsert.push(var_idx);
                    continue;
                }
            } else {
                reinsert.push(var_idx);
                continue;
            }

            break Some(var);
        };

        // Re-insert skipped (but unfixed) variables
        for &var_idx in reinsert.iter() {
            heap.insert(var_idx, &self.var_activity);
        }

        result
    }

    /// Input-order: first unfixed variable in annotation-specified order.
    /// Falls back to creation order if no search_vars specified.
    fn select_input_order(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        ctx: &dyn SolverContext,
    ) -> Option<IntVarId> {
        if self.search_vars.is_empty() {
            // Fallback: iterate in creation order
            for var_idx in 0..trail.num_vars() {
                let var = IntVarId(var_idx as u32);
                if trail.ub(var) - trail.lb(var) < 1 {
                    continue;
                }
                if let Some(ge_lit) = encoder.lookup_ge(var, trail.lb(var) + 1) {
                    if ctx.value(ge_lit.variable()).is_none() {
                        return Some(var);
                    }
                }
            }
            return None;
        }

        for &var in &self.search_vars {
            if trail.ub(var) - trail.lb(var) < 1 {
                continue;
            }
            if let Some(ge_lit) = encoder.lookup_ge(var, trail.lb(var) + 1) {
                if ctx.value(ge_lit.variable()).is_none() {
                    return Some(var);
                }
            }
        }
        // All annotation vars are fixed; fall through to remaining vars
        for var_idx in 0..trail.num_vars() {
            let var = IntVarId(var_idx as u32);
            if var_idx < self.is_search_var.len() && self.is_search_var[var_idx] {
                continue;
            }
            if trail.ub(var) - trail.lb(var) < 1 {
                continue;
            }
            if let Some(ge_lit) = encoder.lookup_ge(var, trail.lb(var) + 1) {
                if ctx.value(ge_lit.variable()).is_none() {
                    return Some(var);
                }
            }
        }
        None
    }
}
