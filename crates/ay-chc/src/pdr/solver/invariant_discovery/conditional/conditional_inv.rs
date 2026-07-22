// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover conditional invariants proactively.
    ///
    /// This discovers invariants of the form:
    ///   (pivot_var <= threshold => other_var = init_value) AND
    ///   (pivot_var > threshold => other_var = pivot_var)
    ///
    /// These arise when one variable controls a phase transition:
    /// - Before the threshold, another variable stays constant
    /// - After the threshold, both variables track each other
    ///
    /// Example: s_disj_ite patterns where:
    /// - A increments from 0 to 100
    /// - B = 50 while A <= 50, then B increments with A
    /// - At A = 100, B = 100 (the property)
    pub(in crate::pdr::solver) fn discover_conditional_invariants(&mut self) {
        let _ = self.discover_conditional_invariants_impl(false);
    }

    /// Run the conditional pass as an early simple-loop probe.
    ///
    /// The full conditional pass can keep exploring sibling thresholds after it has
    /// already found the proof-carrying phase invariant. For small ITE loops, stop
    /// after the first admitted conditional invariant so startup can try the normal
    /// direct safety proof while there is still validation budget left.
    pub(in crate::pdr::solver) fn discover_conditional_invariants_early_probe(&mut self) -> bool {
        self.discover_conditional_invariants_impl(true)
    }

    fn discover_conditional_invariants_impl(&mut self, stop_after_first_added: bool) -> bool {
        let mut added_any = false;
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if stop_after_first_added && !self.conditional_invariant_early_probe_supported(pred.id)
            {
                continue;
            }

            // Skip predicates without fact clauses (no initial state)
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Need at least 2 variables
            if canonical_vars.len() < 2 {
                continue;
            }

            // Get initial values for this predicate
            let init_values = self.get_init_values(pred.id);

            // Find threshold conditions from transition clauses
            let thresholds = self.extract_threshold_conditions(pred.id);
            if self.config.verbose && !thresholds.is_empty() {
                safe_eprintln!(
                    "PDR: Found {} thresholds for conditional invariant discovery: {:?}",
                    thresholds.len(),
                    thresholds
                );
            }
            if thresholds.is_empty() {
                continue;
            }

            // For each pair of integer variables, check for conditional invariants
            for i in 0..canonical_vars.len() {
                if self.is_cancelled() {
                    return added_any;
                }
                for j in 0..canonical_vars.len() {
                    if i == j {
                        continue;
                    }

                    let pivot_var = &canonical_vars[i];
                    let other_var = &canonical_vars[j];

                    // Only check integer variables
                    if !matches!(pivot_var.sort, ChcSort::Int)
                        || !matches!(other_var.sort, ChcSort::Int)
                    {
                        continue;
                    }

                    // Get init values
                    let init_other = match init_values.get(&other_var.name) {
                        Some(bounds) if bounds.min == bounds.max => bounds.min,
                        _ => continue,
                    };

                    // For each threshold on the pivot variable, test the conditional invariant
                    for &threshold in &thresholds {
                        // Test: (pivot <= threshold => other = init_other) AND
                        //       (pivot > threshold => other = pivot)
                        if self
                            .is_conditional_equality_invariant(pred.id, i, j, threshold, init_other)
                        {
                            // Build the conditional invariant:
                            // (pivot <= threshold => other = init_other) AND (pivot > threshold => other = pivot)
                            // Which is equivalent to:
                            // (pivot > threshold OR other = init_other) AND (pivot <= threshold OR other = pivot)
                            let pivot_expr = ChcExpr::var(pivot_var.clone());
                            let other_expr = ChcExpr::var(other_var.clone());
                            let threshold_const = ChcExpr::Int(threshold);

                            let below_condition =
                                ChcExpr::le(pivot_expr.clone(), threshold_const.clone());
                            let above_condition = ChcExpr::gt(pivot_expr.clone(), threshold_const);
                            let other_eq_init =
                                ChcExpr::eq(other_expr.clone(), ChcExpr::Int(init_other));
                            let other_eq_pivot = ChcExpr::eq(other_expr, pivot_expr);

                            // (below => other=init) AND (above => other=pivot)
                            let impl1 = ChcExpr::or(ChcExpr::not(below_condition), other_eq_init);
                            let impl2 = ChcExpr::or(ChcExpr::not(above_condition), other_eq_pivot);
                            let conditional_invariant = ChcExpr::and(impl1, impl2);

                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered conditional invariant for pred {}: ({} <= {} => {} = {}) AND ({} > {} => {} = {})",
                                    pred.id.index(),
                                    pivot_var.name, threshold,
                                    other_var.name, init_other,
                                    pivot_var.name, threshold,
                                    other_var.name, pivot_var.name
                                );
                            }

                            // Add to frame 1. The early algebraic path is restricted to
                            // self-loop-only predicates, and the conditional checker above
                            // has already checked all facts and preserving self-loops.
                            // Strict final validation still verifies the returned model.
                            let added = if stop_after_first_added {
                                self.add_discovered_invariant_algebraic(
                                    pred.id,
                                    conditional_invariant,
                                    1,
                                )
                            } else {
                                self.add_discovered_invariant(pred.id, conditional_invariant, 1)
                            };
                            if added {
                                added_any = true;
                                if stop_after_first_added {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }

        added_any
    }

    fn conditional_invariant_early_probe_supported(&self, predicate: PredicateId) -> bool {
        let Some(canonical_vars) = self.canonical_vars(predicate) else {
            return false;
        };

        let mut checked_any_self_loop = false;
        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.is_empty() {
                continue;
            }

            let crate::ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
                return false;
            };
            if *head_pred != predicate || head_args.len() != canonical_vars.len() {
                return false;
            }
            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate || body_args.len() != canonical_vars.len() {
                return false;
            }

            checked_any_self_loop = true;
        }

        checked_any_self_loop
    }

    /// Extract threshold constants from transition constraints.
    ///
    /// Looks for patterns like `var <= K` or `var > K` or `var < K` in constraints.
    pub(in crate::pdr::solver) fn extract_threshold_conditions(
        &self,
        predicate: PredicateId,
    ) -> Vec<i128> {
        let mut thresholds = FxHashSet::default();

        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses
            if clause.body.predicates.is_empty() {
                continue;
            }

            if let Some(constraint) = &clause.body.constraint {
                Self::extract_thresholds_from_expr(constraint, &mut thresholds);
            }
        }

        // Sort for deterministic iteration order
        let mut result: Vec<i128> = thresholds.into_iter().collect();
        result.sort_unstable();
        result
    }

    /// Recursively extract threshold constants from an expression.
    pub(in crate::pdr::solver) fn extract_thresholds_from_expr(
        expr: &ChcExpr,
        thresholds: &mut FxHashSet<i128>,
    ) {
        match expr {
            // Look for patterns like x <= K, x < K, x >= K, x > K
            ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt, args) if args.len() == 2 => {
                // Check if one side is a constant (handles Op(Neg,[Int(n)]) via as_i128())
                if let Some(k) = args[0].as_i128() {
                    thresholds.insert(k);
                    // Also try k-1 and k+1 for < and > variations
                    thresholds.insert(k.saturating_sub(1));
                    thresholds.insert(k.saturating_add(1));
                }
                if let Some(k) = args[1].as_i128() {
                    thresholds.insert(k);
                    thresholds.insert(k.saturating_sub(1));
                    thresholds.insert(k.saturating_add(1));
                }
            }
            ChcExpr::Op(_, args) => {
                for arg in args {
                    Self::extract_thresholds_from_expr(arg, thresholds);
                }
            }
            _ => {}
        }
    }

    /// Check if a conditional equality invariant holds.
    ///
    /// Tests if for predicate P(x1, ..., xn):
    ///   (x[pivot_idx] <= threshold => x[other_idx] = init_other) AND
    ///   (x[pivot_idx] > threshold => x[other_idx] = x[pivot_idx])
    ///
    /// The invariant must:
    /// 1. Hold for all initial states
    /// 2. Be preserved by all transitions
    pub(in crate::pdr::solver) fn is_conditional_equality_invariant(
        &mut self,
        predicate: PredicateId,
        pivot_idx: usize,
        other_idx: usize,
        threshold: i128,
        init_other: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        if pivot_idx >= canonical_vars.len() || other_idx >= canonical_vars.len() {
            return false;
        }

        let _pivot_var = &canonical_vars[pivot_idx];
        let _other_var = &canonical_vars[other_idx];

        // 1. Check that the invariant holds for initial states
        // For all fact clauses, check: init satisfies the conditional invariant
        for clause in self.problem.clauses_defining(predicate) {
            // Only check fact clauses (no body predicates = initial state)
            if !clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            let pivot_init = &head_args[pivot_idx];
            let other_init = &head_args[other_idx];

            // The invariant condition for init state:
            // (pivot <= threshold => other = init_other) AND (pivot > threshold => other = pivot)
            let pivot_le_threshold = ChcExpr::le(pivot_init.clone(), ChcExpr::Int(threshold));
            let other_eq_init_const = ChcExpr::eq(other_init.clone(), ChcExpr::Int(init_other));
            let pivot_gt_threshold = ChcExpr::gt(pivot_init.clone(), ChcExpr::Int(threshold));
            let other_eq_pivot = ChcExpr::eq(other_init.clone(), pivot_init.clone());

            // Check: (pivot_le_threshold => other_eq_init) AND (pivot_gt_threshold => other_eq_pivot)
            // Violates if: (pivot_le_threshold AND NOT other_eq_init) OR (pivot_gt_threshold AND NOT other_eq_pivot)
            let constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            let violates_below = ChcExpr::and(
                ChcExpr::and(constraint.clone(), pivot_le_threshold),
                ChcExpr::not(other_eq_init_const),
            );
            let violates_above = ChcExpr::and(
                ChcExpr::and(constraint, pivot_gt_threshold),
                ChcExpr::not(other_eq_pivot),
            );

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&violates_below, std::time::Duration::from_millis(200))
            {
                SmtResult::Sat(_) => return false, // Init violates below-threshold condition
                SmtResult::Unknown => return false,
                _ => {}
            }

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&violates_above, std::time::Duration::from_millis(200))
            {
                SmtResult::Sat(_) => return false, // Init violates above-threshold condition
                SmtResult::Unknown => return false,
                _ => {}
            }
        }

        // 2. Check that the invariant is preserved by transitions
        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses
            if clause.body.predicates.is_empty() {
                continue;
            }

            // Only handle self-transitions for now
            if clause.body.predicates.len() != 1 {
                continue; // Skip hyperedges
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }

            if body_args.len() != canonical_vars.len() {
                return false;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            let body_pivot = &body_args[pivot_idx];
            let body_other = &body_args[other_idx];
            let head_pivot = &head_args[pivot_idx];
            let head_other = &head_args[other_idx];

            let constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Pre-state invariant for below threshold:
            // body_pivot <= threshold => body_other = init_other
            let body_pivot_le = ChcExpr::le(body_pivot.clone(), ChcExpr::Int(threshold));
            let body_other_eq_init = ChcExpr::eq(body_other.clone(), ChcExpr::Int(init_other));
            let pre_below = ChcExpr::or(ChcExpr::not(body_pivot_le.clone()), body_other_eq_init);

            // Pre-state invariant for above threshold:
            // body_pivot > threshold => body_other = body_pivot
            let body_pivot_gt = ChcExpr::gt(body_pivot.clone(), ChcExpr::Int(threshold));
            let body_other_eq_pivot = ChcExpr::eq(body_other.clone(), body_pivot.clone());
            let pre_above = ChcExpr::or(ChcExpr::not(body_pivot_gt), body_other_eq_pivot);

            let pre_invariant = ChcExpr::and(pre_below, pre_above);

            // Post-state requirement for below threshold:
            // head_pivot <= threshold => head_other = init_other
            let head_pivot_le = ChcExpr::le(head_pivot.clone(), ChcExpr::Int(threshold));
            let head_other_eq_init = ChcExpr::eq(head_other.clone(), ChcExpr::Int(init_other));

            // Post-state requirement for above threshold:
            // head_pivot > threshold => head_other = head_pivot
            let head_pivot_gt = ChcExpr::gt(head_pivot.clone(), ChcExpr::Int(threshold));
            let head_other_eq_head_pivot = ChcExpr::eq(head_other.clone(), head_pivot.clone());

            // Check below-threshold preservation:
            // pre_invariant AND constraint AND head_pivot <= threshold AND NOT(head_other = init_other)
            let violates_post_below = ChcExpr::and(
                ChcExpr::and(
                    ChcExpr::and(pre_invariant.clone(), constraint.clone()),
                    head_pivot_le,
                ),
                ChcExpr::not(head_other_eq_init),
            );

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&violates_post_below, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => return false,
                SmtResult::Unknown => return false,
                _ => {}
            }

            // Check above-threshold preservation:
            // pre_invariant AND constraint AND head_pivot > threshold AND NOT(head_other = head_pivot)
            let violates_post_above = ChcExpr::and(
                ChcExpr::and(ChcExpr::and(pre_invariant, constraint), head_pivot_gt),
                ChcExpr::not(head_other_eq_head_pivot),
            );

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&violates_post_above, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => return false,
                SmtResult::Unknown => return false,
                _ => {}
            }
        }

        // If zero self-loops were checked, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }
        true
    }
}
