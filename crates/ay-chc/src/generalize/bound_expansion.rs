// Copyright 2026 Andrew Yates
// Author: Andrew Yates
//
// Licensed under the Apache License, Version 2.0

//! Bound expansion and Farkas combination generalizers.
//!
//! Extracted from `weakening.rs` to keep file sizes under 500 lines.

use super::*;

/// Bound expansion generalizer: expands constant bounds in inequalities.
///
/// For constraints like `x < 5`, tries weakening to `x < 6`, `x < 7`, etc.
/// using binary search to find the weakest inductive bound.
///
/// This is useful when DropLiteralGeneralizer cannot drop a bound entirely,
/// but the specific constant is overly restrictive.
///
/// # Examples
///
/// - `x < 5` → `x < 10` (if `x < 10` is still inductive)
/// - `y >= 3` → `y >= 1` (if `y >= 1` is still inductive)
///
/// # Algorithm
///
/// For each inequality with a constant bound:
/// 1. Identify the direction to expand (toward weaker constraint)
/// 2. Binary search to find the weakest inductive bound
/// 3. Apply if the search finds a weaker bound than the original
///
/// Reference: Z3's range weakening in PDR generalization.
pub(crate) struct BoundExpansionGeneralizer {
    /// Maximum search distance from original bound
    pub(super) max_search_distance: i128,
}

impl Default for BoundExpansionGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl BoundExpansionGeneralizer {
    /// Create a new bound expansion generalizer with default settings.
    pub(crate) fn new() -> Self {
        Self {
            max_search_distance: 1000,
        }
    }

    /// Try to expand a bound constraint.
    ///
    /// Returns the weakest inductive bound, or None if no expansion is possible.
    fn try_expand_bound(
        &self,
        lit: &ChcExpr,
        other_conjuncts: &[ChcExpr],
        level: u32,
        ts: &mut dyn TransitionSystemRef,
    ) -> Option<ChcExpr> {
        use crate::expr::ChcOp;

        // Match inequality patterns: (op var const) or (op const var)
        let (op, var_expr, orig_const, var_on_left) = match lit {
            ChcExpr::Op(op @ (ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge), args)
                if args.len() == 2 =>
            {
                match (args[0].as_ref(), args[1].as_ref()) {
                    // var op const (e.g., x < 5)
                    (var, ChcExpr::Int(c)) if !matches!(var, ChcExpr::Int(_)) => {
                        (*op, var.clone(), *c, true)
                    }
                    // const op var (e.g., 5 < x)
                    (ChcExpr::Int(c), var) if !matches!(var, ChcExpr::Int(_)) => {
                        (*op, var.clone(), *c, false)
                    }
                    _ => return None,
                }
            }
            _ => return None,
        };

        // Determine search direction and create candidate formula generator
        // We want to WEAKEN the constraint, which means:
        // - x < c: increase c (blocks fewer states)
        // - x > c: decrease c (blocks fewer states)
        // - x <= c: increase c (blocks fewer states)
        // - x >= c: decrease c (blocks fewer states)
        let (search_min, search_max, create_formula): (i128, i128, Box<dyn Fn(i128) -> ChcExpr>) =
            match (&op, var_on_left) {
                // x < c: weaken by increasing c
                (ChcOp::Lt, true) => {
                    let var = var_expr;
                    (
                        orig_const.saturating_add(1),
                        orig_const.saturating_add(self.max_search_distance),
                        Box::new(move |c| ChcExpr::lt(var.clone(), ChcExpr::Int(c))),
                    )
                }
                // c < x: weaken by decreasing c (same as x > c)
                (ChcOp::Lt, false) => {
                    let var = var_expr;
                    (
                        orig_const.saturating_sub(self.max_search_distance),
                        orig_const.saturating_sub(1),
                        Box::new(move |c| ChcExpr::gt(var.clone(), ChcExpr::Int(c))),
                    )
                }
                // x > c: weaken by decreasing c
                (ChcOp::Gt, true) => {
                    let var = var_expr;
                    (
                        orig_const.saturating_sub(self.max_search_distance),
                        orig_const.saturating_sub(1),
                        Box::new(move |c| ChcExpr::gt(var.clone(), ChcExpr::Int(c))),
                    )
                }
                // c > x: weaken by increasing c (same as x < c)
                (ChcOp::Gt, false) => {
                    let var = var_expr;
                    (
                        orig_const.saturating_add(1),
                        orig_const.saturating_add(self.max_search_distance),
                        Box::new(move |c| ChcExpr::lt(var.clone(), ChcExpr::Int(c))),
                    )
                }
                // x <= c: weaken by increasing c
                (ChcOp::Le, true) => {
                    let var = var_expr;
                    (
                        orig_const.saturating_add(1),
                        orig_const.saturating_add(self.max_search_distance),
                        Box::new(move |c| ChcExpr::le(var.clone(), ChcExpr::Int(c))),
                    )
                }
                // c <= x: weaken by decreasing c (same as x >= c)
                (ChcOp::Le, false) => {
                    let var = var_expr;
                    (
                        orig_const.saturating_sub(self.max_search_distance),
                        orig_const.saturating_sub(1),
                        Box::new(move |c| ChcExpr::ge(var.clone(), ChcExpr::Int(c))),
                    )
                }
                // x >= c: weaken by decreasing c
                (ChcOp::Ge, true) => {
                    let var = var_expr;
                    (
                        orig_const.saturating_sub(self.max_search_distance),
                        orig_const.saturating_sub(1),
                        Box::new(move |c| ChcExpr::ge(var.clone(), ChcExpr::Int(c))),
                    )
                }
                // c >= x: weaken by increasing c (same as x <= c)
                (ChcOp::Ge, false) => {
                    let var = var_expr;
                    (
                        orig_const.saturating_add(1),
                        orig_const.saturating_add(self.max_search_distance),
                        Box::new(move |c| ChcExpr::le(var.clone(), ChcExpr::Int(c))),
                    )
                }
                _ => return None,
            };

        // Binary search for the weakest inductive bound
        // We're searching for the extreme value where the constraint is still inductive
        let best_bound = self.binary_search_bound(
            search_min,
            search_max,
            &create_formula,
            other_conjuncts,
            level,
            ts,
        )?;

        // Only return if we found a weaker bound
        if best_bound != orig_const {
            Some(create_formula(best_bound))
        } else {
            None
        }
    }

    /// Binary search to find the most extreme inductive bound.
    fn binary_search_bound(
        &self,
        search_min: i128,
        search_max: i128,
        create_formula: &dyn Fn(i128) -> ChcExpr,
        other_conjuncts: &[ChcExpr],
        level: u32,
        ts: &mut dyn TransitionSystemRef,
    ) -> Option<i128> {
        if search_min > search_max {
            return None;
        }

        // First check if the extreme bound is inductive
        let extreme = if search_max > search_min {
            search_max
        } else {
            search_min
        };

        let extreme_formula = create_formula(extreme);
        let mut test_conjuncts: Vec<ChcExpr> = other_conjuncts.to_vec();
        test_conjuncts.push(extreme_formula);
        let test_expr = ChcExpr::and_all(test_conjuncts.iter().cloned());

        if ts.check_inductive(&test_expr, level) {
            // Extreme bound is inductive - return it
            return Some(extreme);
        }

        // Binary search for the best bound
        let mut lo = search_min;
        let mut hi = search_max;
        let mut best = None;

        while lo <= hi {
            let mid = lo + (hi - lo) / 2;

            let mid_formula = create_formula(mid);
            let mut test_conjuncts: Vec<ChcExpr> = other_conjuncts.to_vec();
            test_conjuncts.push(mid_formula);
            let test_expr = ChcExpr::and_all(test_conjuncts.iter().cloned());

            if ts.check_inductive(&test_expr, level) {
                // This bound is inductive - try to find a weaker one
                best = Some(mid);
                // Search toward the extreme (weaker direction)
                if search_max > search_min {
                    lo = mid + 1;
                } else {
                    hi = mid - 1;
                }
            } else {
                // This bound is not inductive - search toward the original
                if search_max > search_min {
                    hi = mid - 1;
                } else {
                    lo = mid + 1;
                }
            }
        }

        best
    }
}

impl LemmaGeneralizer for BoundExpansionGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();

        if conjuncts.is_empty() {
            return lemma.clone();
        }

        let mut result_conjuncts = conjuncts.clone();
        let mut any_changed = false;

        for i in 0..conjuncts.len() {
            // Get other conjuncts (excluding the one we're trying to expand)
            let other_conjuncts: Vec<ChcExpr> = result_conjuncts
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, c)| c.clone())
                .collect();

            // Try to expand the bound
            if let Some(expanded) =
                self.try_expand_bound(&result_conjuncts[i], &other_conjuncts, level, ts)
            {
                result_conjuncts[i] = expanded;
                any_changed = true;
            }
        }

        if any_changed {
            ChcExpr::and_all(result_conjuncts.iter().cloned())
        } else {
            lemma.clone()
        }
    }

    fn name(&self) -> &'static str {
        "bound-expansion"
    }
}

/// Farkas combination generalizer: combines linear constraints using Farkas coefficients.
///
/// When the lemma contains multiple linear inequalities, this generalizer attempts
/// to combine them using Farkas' lemma to produce a single, more general constraint.
///
/// # When to Use
///
/// Use this generalizer when dealing with linear arithmetic constraints.
/// It's particularly effective when:
/// - Multiple bounds on related variables exist
/// - Transitivity chains can be exploited (e.g., x ≤ y, y ≤ z → x ≤ z)
/// - Opposite-sign coefficients allow variable elimination
///
/// # Examples
///
/// Input: `x ≤ 5 AND y ≥ x AND y ≤ 3`
/// - Can combine to derive tighter bounds
/// - May produce: `x ≤ 3` (if y ≥ x and y ≤ 3, then x ≤ 3)
///
/// # Design Note
///
/// This is PDR's Phase 1d generalization. It uses the Farkas module's
/// `farkas_combine` function which implements multiple combination strategies:
/// 1. Equal weights (direct sum)
/// 2. Variable elimination
/// 3. Transitivity chains
/// 4. Bound tightening
///
/// Reference: PDR's Phase 1d (lines 7421-7440 in pdr.rs)
pub(crate) struct FarkasGeneralizer;

impl Default for FarkasGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl FarkasGeneralizer {
    /// Create a new Farkas combination generalizer.
    pub(crate) fn new() -> Self {
        Self
    }
}

impl LemmaGeneralizer for FarkasGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();

        // Need at least 2 constraints to combine
        if conjuncts.len() < 2 {
            return lemma.clone();
        }

        // Try Farkas combination
        if let Some(fc) = crate::farkas::farkas_combine(&conjuncts) {
            // Verify the combined constraint is still inductive
            if ts.check_inductive(&fc.combined, level) {
                return fc.combined;
            }
        }

        // Farkas combination didn't work or wasn't inductive
        lemma.clone()
    }

    fn name(&self) -> &'static str {
        "farkas-combination"
    }
}
