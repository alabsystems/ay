// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Search heuristics for CP-SAT variable/value selection.
//!
//! This module provides multiple search strategies for selecting the next
//! variable to branch on during solving. The choice of heuristic significantly
//! affects solving performance on combinatorial problems.
//!
//! # Implemented Heuristics
//!
//! - **FirstFail**: Choose the variable with the smallest domain (fewest
//!   remaining values). Classic CP heuristic from Haralick & Elliott (1980).
//!
//! - **DomWDeg**: Choose the variable minimizing `domain_size / weight`,
//!   where weight is the sum of failure counts of constraints involving the
//!   variable. Boussemart et al. "Boosting Systematic Search by Weighting
//!   Constraints" (ECAI 2004).
//!
//! - **ActivityBased**: Choose the variable with the highest activity score,
//!   incremented on each conflict involvement and decayed periodically.
//!   Similar to VSIDS but applied to integer variables. Michel & Van Hentenryck
//!   "Activity-Based Search for Black-Box Constraint Programming Solvers"
//!   (CPAIOR 2012).

use std::cell::RefCell;

use crate::encoder::IntegerEncoder;
use crate::heap::VarHeap;
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;
use ay_sat::{Literal, SolverContext};

// Variable selection strategies (select_first_fail, select_dom_wdeg, etc.)
#[path = "search_select.rs"]
mod search_select;

/// Search strategy for variable selection.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum SearchStrategy {
    /// Smallest domain first (classic first-fail).
    FirstFail,
    /// Domain size / weighted degree (failure-directed).
    #[default]
    DomWDeg,
    /// Highest activity score (VSIDS-like for integer variables).
    Activity,
    /// Variables in annotation-specified order (first unfixed wins).
    InputOrder,
}

/// Value selection strategy for branching.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum ValueChoice {
    /// Try lower bound first: x = lb (¬[x >= lb+1]).
    IndomainMin,
    /// Try upper bound first: x = ub ([x >= ub]).
    IndomainMax,
    /// Binary domain split: try x <= mid first (¬[x >= mid+1]).
    /// Most common MiniZinc strategy for competition models.
    /// Default: halves domain each decision → O(log d) vs O(d) for IndomainMin.
    #[default]
    IndomainSplit,
    /// Reverse binary domain split: try x >= mid+1 first ([x >= mid+1]).
    /// Tries upper half first — useful for maximization objectives.
    IndomainReverseSplit,
}

/// Search state: conflict weights, activity scores, and priority heap.
///
/// For Activity strategy, a binary max-heap provides O(log n) variable
/// selection instead of O(n) linear scans (#5812).
pub(crate) struct SearchState {
    strategy: SearchStrategy,
    value_choice: ValueChoice,
    /// Annotation-specified variable ordering for InputOrder strategy.
    search_vars: Vec<IntVarId>,
    /// O(1) lookup: `is_search_var[v]` = true iff `v` is in `search_vars`.
    /// Replaces O(n) `.contains()` in `select_input_order` fallback loop.
    is_search_var: Vec<bool>,
    /// Weight per propagator (for dom/wdeg). Incremented on conflict.
    propagator_weights: Vec<u64>,
    /// Cached per-variable weighted degree: `cached_wdeg[v]` = sum of
    /// `propagator_weights[p]` for all propagators p watching variable v.
    /// Updated incrementally in `on_conflict()` instead of recomputing
    /// from `var_to_propagators` each selection (O(1) vs O(degree)).
    cached_wdeg: Vec<f64>,
    /// Activity score per integer variable.
    var_activity: Vec<f64>,
    decay_factor: f64,
    /// Inverse bump increment (grows as 1/(decay^conflicts), VSIDS trick).
    activity_increment: f64,
    conflict_count: u64,
    /// Priority heap for O(log n) selection. RefCell: Extension trait
    /// requires &self for suggest_decision but heap pop needs mutation.
    var_heap: RefCell<VarHeap>,
    /// True after backtrack invalidates heap ordering.
    heap_stale: std::cell::Cell<bool>,
    /// Workspace: variables to re-insert into the heap after selection.
    /// Avoids per-call Vec allocation in select_*_heap methods.
    ws_reinsert: RefCell<Vec<u32>>,
    num_vars: usize,
}

impl SearchState {
    /// Create a new search state for the given number of propagators and variables.
    ///
    /// Precomputes a variable-to-propagator index from the propagator list
    /// so that weighted degree lookups are O(degree) not O(total_propagators).
    pub(crate) fn new(
        strategy: SearchStrategy,
        value_choice: ValueChoice,
        search_vars: Vec<IntVarId>,
        propagators: &[Box<dyn crate::propagator::Propagator>],
        num_vars: usize,
    ) -> Self {
        let num_propagators = propagators.len();
        let mut var_to_propagators = vec![Vec::new(); num_vars];
        for (i, prop) in propagators.iter().enumerate() {
            for &var in prop.variables() {
                let idx = var.0 as usize;
                if idx < num_vars {
                    var_to_propagators[idx].push(i);
                }
            }
        }
        // Initialize cached wdeg: each propagator starts with weight 1,
        // so wdeg(v) = number of propagators watching v (min 1).
        let cached_wdeg: Vec<f64> = var_to_propagators
            .iter()
            .map(|props| (props.len().max(1)) as f64)
            .collect();

        let activity = vec![0.0; num_vars];

        // Build heap with strategy-appropriate scores
        let heap_scores: &[f64] = match strategy {
            SearchStrategy::DomWDeg => &cached_wdeg,
            _ => &activity,
        };
        let var_heap = RefCell::new(VarHeap::with_all(num_vars, heap_scores));

        let mut is_search_var = vec![false; num_vars];
        for &v in &search_vars {
            let idx = v.0 as usize;
            if idx < num_vars {
                is_search_var[idx] = true;
            }
        }

        Self {
            strategy,
            value_choice,
            search_vars,
            is_search_var,
            propagator_weights: vec![1; num_propagators],
            cached_wdeg,
            var_activity: activity,
            decay_factor: 0.95,
            activity_increment: 1.0,
            conflict_count: 0,
            var_heap,
            heap_stale: std::cell::Cell::new(false),
            ws_reinsert: RefCell::new(Vec::with_capacity(num_vars)),
            num_vars,
        }
    }

    /// Record that propagator `idx` caused a conflict.
    ///
    /// `variables` must be ALL variables of the conflicting propagator
    /// (from `Propagator::variables()`). Updates cached wdeg, activity
    /// scores, and the heap with strategy-appropriate keys.
    pub(crate) fn on_conflict(&mut self, propagator_idx: usize, variables: &[IntVarId]) {
        // Bump propagator weight (dom/wdeg)
        if propagator_idx < self.propagator_weights.len() {
            self.propagator_weights[propagator_idx] += 1;
        }

        // Update cached wdeg, activity, and heap for all variables of this
        // propagator. cached_wdeg[v] += 1 because propagator_weights[p] grew.
        let use_wdeg_heap = self.strategy == SearchStrategy::DomWDeg;
        let use_activity_heap = self.strategy == SearchStrategy::Activity;

        for &var in variables {
            let idx = var.0 as usize;
            if idx < self.num_vars {
                self.cached_wdeg[idx] += 1.0;
                self.var_activity[idx] += self.activity_increment;

                if use_wdeg_heap {
                    self.var_heap
                        .borrow_mut()
                        .increase_key(var.0, &self.cached_wdeg);
                } else if use_activity_heap {
                    self.var_heap
                        .borrow_mut()
                        .increase_key(var.0, &self.var_activity);
                }
            }
        }

        // Decay: increase the bump increment so future bumps are larger,
        // effectively decaying old activities relative to new ones.
        self.conflict_count += 1;
        self.activity_increment /= self.decay_factor;

        // Rescale if activities get too large (prevent floating-point overflow)
        if self.activity_increment > 1e100 {
            let scale = 1e-100;
            for act in &mut self.var_activity {
                *act *= scale;
            }
            self.activity_increment *= scale;
            // Rebuild heap after rescaling (all scores changed)
            self.heap_stale.set(true);
        }
    }

    /// Notify search state that the solver backtracked.
    /// Marks the heap as stale so the next `select_variable` call rebuilds it.
    pub(crate) fn notify_backtrack(&mut self) {
        self.heap_stale.set(true);
    }

    /// Rebuild the variable heap with all variables, using strategy-appropriate
    /// scores: wdeg for DomWDeg, activity for Activity.
    fn rebuild_heap(&self) {
        let scores = self.heap_scores();
        self.var_heap
            .borrow_mut()
            .reset_with_all(self.num_vars, scores);
        self.heap_stale.set(false);
    }

    /// Return the score array used for heap ordering (strategy-dependent).
    #[inline]
    fn heap_scores(&self) -> &[f64] {
        match self.strategy {
            SearchStrategy::DomWDeg => &self.cached_wdeg,
            _ => &self.var_activity,
        }
    }

    // Variable selection strategies (select_variable, select_first_fail,
    // select_dom_wdeg, select_dom_wdeg_heap, select_activity_heap,
    // select_input_order) moved to search_select.rs.

    /// Create a decision literal for the selected variable.
    /// Respects `value_choice`: IndomainMin tries lower bound, IndomainMax
    /// tries upper bound.
    pub(crate) fn make_decision(
        &self,
        var: IntVarId,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        ctx: &dyn SolverContext,
    ) -> Option<Literal> {
        match self.value_choice {
            ValueChoice::IndomainMin => {
                let lb = trail.lb(var);
                let ge_lit = encoder.lookup_ge(var, lb + 1)?;
                if ctx.value(ge_lit.variable()).is_some() {
                    return None;
                }
                // Decide ¬[x >= lb+1] → x <= lb (try lower bound first)
                Some(ge_lit.negated())
            }
            ValueChoice::IndomainMax => {
                let ub = trail.ub(var);
                let ge_lit = encoder.lookup_ge(var, ub)?;
                if ctx.value(ge_lit.variable()).is_some() {
                    return None;
                }
                // Decide [x >= ub] → x >= ub (try upper bound first)
                Some(ge_lit)
            }
            ValueChoice::IndomainSplit => {
                let lb = trail.lb(var);
                let ub = trail.ub(var);
                let mid = lb + (ub - lb) / 2;
                // Decide ¬[x >= mid+1] → x <= mid (try lower half first)
                let ge_lit = encoder.lookup_ge(var, mid + 1)?;
                if ctx.value(ge_lit.variable()).is_some() {
                    return None;
                }
                Some(ge_lit.negated())
            }
            ValueChoice::IndomainReverseSplit => {
                let lb = trail.lb(var);
                let ub = trail.ub(var);
                let mid = lb + (ub - lb) / 2;
                // Decide [x >= mid+1] → x >= mid+1 (try upper half first)
                let ge_lit = encoder.lookup_ge(var, mid + 1)?;
                if ctx.value(ge_lit.variable()).is_some() {
                    return None;
                }
                Some(ge_lit)
            }
        }
    }
}

#[cfg(test)]
#[path = "search_tests.rs"]
mod tests;
