// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Entry value computation and evaluation for difference invariant propagation.

use super::*;

impl PdrSolver {
    /// Compute entry values for a target predicate via a transition from a source predicate.
    /// Uses source frame invariants + transition constraint to determine entry values.
    pub(in crate::pdr::solver) fn compute_entry_values_from_transition(
        &mut self,
        clause: &HornClause,
        source_pred: PredicateId,
        target_pred: PredicateId,
    ) -> FxHashMap<String, InitIntBounds> {
        let mut entry_values = FxHashMap::default();

        let source_vars = match self.canonical_vars(source_pred) {
            Some(v) => v.to_vec(),
            None => return entry_values,
        };

        let target_vars = match self.canonical_vars(target_pred) {
            Some(v) => v.to_vec(),
            None => return entry_values,
        };

        let (_, source_args) = &clause.body.predicates[0];
        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
            crate::ClauseHead::False => return entry_values,
        };

        // Collect source frame invariants (equality and bound invariants)
        let mut source_frame_constraints: Vec<ChcExpr> = Vec::new();
        if self.frames.len() > 1 {
            for lemma in &self.frames[1].lemmas {
                if lemma.predicate == source_pred {
                    source_frame_constraints.push(lemma.formula.clone());
                }
            }
        }

        // Build variable mapping: source canonical -> source arg variable name.
        // #2492: For expression args, map canonical var to first constituent var.
        let mut source_canon_to_arg: FxHashMap<String, String> = FxHashMap::default();
        for (arg, canon) in source_args.iter().zip(source_vars.iter()) {
            match arg {
                ChcExpr::Var(v) => {
                    source_canon_to_arg.insert(canon.name.clone(), v.name.clone());
                }
                expr => {
                    if let Some(first_var) = expr.vars().into_iter().next() {
                        source_canon_to_arg
                            .entry(canon.name.clone())
                            .or_insert(first_var.name);
                    }
                }
            }
        }

        // Rename source frame constraints to use source arg variable names.
        let renamed_constraints: Vec<ChcExpr> = source_frame_constraints
            .iter()
            .map(|c| c.rename_vars(&source_canon_to_arg))
            .collect();

        // Build inference context.
        //
        // The full source-frame context can become inconsistent with this specific entry edge.
        // If we infer from an UNSAT context, every value is implied vacuously, which can
        // collapse entry bounds to spurious constants (regression #2778).
        //
        // Strategy:
        // 1) Try full context (all source lemmas + transition guard)
        // 2) If UNSAT/UNKNOWN, retry with a linear-safe subset of source lemmas
        // 3) If still UNSAT/UNKNOWN, skip entry inference for this transition
        let mut full_conjuncts = renamed_constraints.clone();
        if let Some(constraint) = &clause.body.constraint {
            full_conjuncts.push(constraint.clone());
        }
        let full_combined_constraint = Self::conjunction_from_vec(full_conjuncts);
        let combined_constraint =
            if self.is_sat_for_entry_value_inference(&full_combined_constraint) {
                full_combined_constraint
            } else {
                let mut relaxed_conjuncts: Vec<ChcExpr> = renamed_constraints
                    .into_iter()
                    .filter(Self::is_entry_value_constraint_safe)
                    .collect();
                if let Some(constraint) = &clause.body.constraint {
                    relaxed_conjuncts.push(constraint.clone());
                }
                let relaxed_combined_constraint = Self::conjunction_from_vec(relaxed_conjuncts);
                if !self.is_sat_for_entry_value_inference(&relaxed_combined_constraint) {
                    return entry_values;
                }
                relaxed_combined_constraint
            };

        // Extract head variable assignments from the transition constraint
        let constraint = clause.body.constraint.as_ref();

        for (head_idx, target_canon) in target_vars.iter().enumerate() {
            if head_idx >= head_args.len() {
                continue;
            }

            let head_arg = &head_args[head_idx];

            // Case 1: head arg is a simple variable - look for it in constraint equalities
            if let ChcExpr::Var(hv) = head_arg {
                // First check if constraint has (= head_var expr) pattern
                if let Some(c) = constraint {
                    if let Some(value) = Self::find_equality_value(c, &hv.name) {
                        // Try to evaluate the value under combined_constraint
                        if let Some(bounds) =
                            self.evaluate_entry_value(&value, &combined_constraint)
                        {
                            entry_values.insert(target_canon.name.clone(), bounds);
                            continue;
                        }
                    }
                }

                // If no explicit equality, try to evaluate the variable directly
                // This handles normalized clauses where head_var is used directly
                // (e.g., SAD(B, 0) instead of SAD(C, D) with (= C B))
                if let Some(bounds) =
                    self.evaluate_entry_value(&ChcExpr::var(hv.clone()), &combined_constraint)
                {
                    entry_values.insert(target_canon.name.clone(), bounds);
                    continue;
                }
            }

            // Case 2: head arg is a constant
            if let ChcExpr::Int(n) = head_arg {
                entry_values.insert(target_canon.name.clone(), InitIntBounds::new(*n));
                continue;
            }

            // Case 3: head arg is a linear expression (+ x k) or (- x k)
            // Part of #1402 Phase 2: Linear head argument support
            // Evaluate the expression directly under combined_constraint
            if Self::is_linear_int_expr(head_arg) {
                if let Some(bounds) = self.evaluate_entry_value(head_arg, &combined_constraint) {
                    entry_values.insert(target_canon.name.clone(), bounds);
                }
            }
        }

        entry_values
    }

    fn conjunction_from_vec(mut conjuncts: Vec<ChcExpr>) -> ChcExpr {
        if conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else if conjuncts.len() == 1 {
            conjuncts.pop().expect("len == 1")
        } else {
            ChcExpr::Op(ChcOp::And, conjuncts.into_iter().map(Arc::new).collect())
        }
    }

    pub(super) fn is_sat_for_entry_value_inference(&mut self, constraint: &ChcExpr) -> bool {
        self.smt.reset();
        let result = self
            .smt
            .check_sat_with_timeout(constraint, std::time::Duration::from_millis(100));
        let is_sat = Self::sat_result_allows_entry_value_inference(&result);
        if !is_sat && self.config.verbose {
            safe_eprintln!(
                "PDR: entry-value inference check returned non-SAT (100ms timeout), skipping"
            );
        }
        is_sat
    }

    pub(super) fn sat_result_allows_entry_value_inference(result: &SmtResult) -> bool {
        matches!(result, SmtResult::Sat(_))
    }

    fn is_entry_value_constraint_safe(expr: &ChcExpr) -> bool {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Real(_, _)
            | ChcExpr::Var(_) => true,
            ChcExpr::Op(op, args) => {
                !matches!(
                    op,
                    ChcOp::Mul
                        | ChcOp::Div
                        | ChcOp::Mod
                        | ChcOp::Ite
                        | ChcOp::Select
                        | ChcOp::Store
                ) && args
                    .iter()
                    .all(|a| Self::is_entry_value_constraint_safe(a.as_ref()))
            }
            ChcExpr::PredicateApp(_, _, _)
            | ChcExpr::FuncApp(_, _, _)
            | ChcExpr::ConstArray(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => false,
        })
    }

    /// Check if an expression is a linear integer expression: var, int, (+ x k), (- x k), (* k x)
    ///
    /// Part of #1402 Phase 2: Linear head argument support
    fn is_linear_int_expr(expr: &ChcExpr) -> bool {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Int(_) | ChcExpr::Var(_) => true,
            ChcExpr::Op(ChcOp::Add | ChcOp::Sub, args) => {
                args.len() == 2 && args.iter().all(|a| Self::is_linear_int_expr(a))
            }
            ChcExpr::Op(ChcOp::Mul, args) => {
                // Allow (k * x) or (x * k) where k is a constant
                args.len() == 2
                    && args.iter().any(|a| matches!(a.as_ref(), ChcExpr::Int(_)))
                    && args.iter().all(|a| Self::is_linear_int_expr(a))
            }
            ChcExpr::Op(ChcOp::Neg, args) => args.len() == 1 && Self::is_linear_int_expr(&args[0]),
            _ => false,
        })
    }

    /// Find the value assigned to a variable in an equality constraint
    pub(in crate::pdr::solver) fn find_equality_value(
        constraint: &ChcExpr,
        var_name: &str,
    ) -> Option<ChcExpr> {
        crate::expr::maybe_grow_expr_stack(|| match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let Some(v) = Self::find_equality_value(arg, var_name) {
                        return Some(v);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let (left, right) = (args[0].as_ref(), args[1].as_ref());

                if let ChcExpr::Var(v) = left {
                    if v.name == var_name {
                        return Some(right.clone());
                    }
                }
                if let ChcExpr::Var(v) = right {
                    if v.name == var_name {
                        return Some(left.clone());
                    }
                }
                None
            }
            _ => None,
        })
    }

    /// Collect all integer constants from an expression.
    ///
    /// Used by evaluate_entry_value to find candidate constants for probing,
    /// instead of using a hardcoded list of values like [0, 1, 1000, 2000].
    ///
    /// Part of #1402: constant-driven entry value inference.
    fn collect_constants_from_expr(expr: &ChcExpr, constants: &mut FxHashSet<i128>) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Int(n) => {
                constants.insert(*n);
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    Self::collect_constants_from_expr(a.as_ref(), constants);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for a in args {
                    Self::collect_constants_from_expr(a.as_ref(), constants);
                }
            }
            ChcExpr::ConstArray(_ks, v) => Self::collect_constants_from_expr(v.as_ref(), constants),
            ChcExpr::Bool(_)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Real(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
        });
    }

    /// Evaluate an expression under a constraint to get bounds
    ///
    /// Part of #1402: This now extracts constants from the constraint to use as
    /// probing candidates, instead of using hardcoded values like [0, 1, 1000, 2000].
    pub(in crate::pdr::solver) fn evaluate_entry_value(
        &mut self,
        expr: &ChcExpr,
        constraint: &ChcExpr,
    ) -> Option<InitIntBounds> {
        match expr {
            ChcExpr::Int(n) => Some(InitIntBounds::new(*n)),
            ChcExpr::Var(v) => {
                // Try to find the value of this variable under the constraint
                // Query: constraint ∧ (var = k) for what values of k?

                // Part of #1402: Extract constants from the constraint instead of using hardcoded values.
                // This allows us to find entry values like 1000 that appear in the transition.
                let mut candidates: FxHashSet<i128> = FxHashSet::default();
                // Always include common baseline constants
                candidates.insert(0);
                candidates.insert(1);
                candidates.insert(-1);
                // Extract constants from the constraint itself
                Self::collect_constants_from_expr(constraint, &mut candidates);
                // Sort for deterministic probing order (smaller values first)
                let mut sorted_candidates: Vec<i128> = candidates.into_iter().collect();
                sorted_candidates.sort_by_key(|x| x.unsigned_abs());

                // First try: check if constraint implies var = k for some k (exact value)
                for test_val in &sorted_candidates {
                    let val_eq = ChcExpr::eq(ChcExpr::var(v.clone()), ChcExpr::Int(*test_val));
                    let query = ChcExpr::and(constraint.clone(), ChcExpr::not(val_eq));

                    self.smt.reset();
                    match self
                        .smt
                        .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                    {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            // constraint => var = test_val
                            return Some(InitIntBounds::new(*test_val));
                        }
                        _ => {}
                    }
                }

                // Second try: find lower bound (check constraint => var >= k)
                // Use sorted_candidates (ascending by abs value) for bound probing
                let mut lower_bound: Option<i128> = None;
                for test_val in &sorted_candidates {
                    let val_ge = ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::Int(*test_val));
                    let query = ChcExpr::and(constraint.clone(), ChcExpr::not(val_ge));

                    self.smt.reset();
                    match self
                        .smt
                        .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                    {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            // constraint => var >= test_val
                            lower_bound =
                                Some(lower_bound.map_or(*test_val, |lb| lb.max(*test_val)));
                        }
                        _ => {}
                    }
                }

                // Third try: find upper bound (check constraint => var <= k)
                // Use sorted_candidates for bound probing
                let mut upper_bound: Option<i128> = None;
                for test_val in &sorted_candidates {
                    let val_le = ChcExpr::le(ChcExpr::var(v.clone()), ChcExpr::Int(*test_val));
                    let query = ChcExpr::and(constraint.clone(), ChcExpr::not(val_le));

                    self.smt.reset();
                    match self
                        .smt
                        .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                    {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            // constraint => var <= test_val
                            upper_bound =
                                Some(upper_bound.map_or(*test_val, |ub| ub.min(*test_val)));
                        }
                        _ => {}
                    }
                }

                if lower_bound.is_some() || upper_bound.is_some() {
                    let mut bounds = InitIntBounds::unbounded();
                    if let Some(lb) = lower_bound {
                        bounds.min = lb;
                    }
                    if let Some(ub) = upper_bound {
                        bounds.max = ub;
                    }
                    return Some(bounds);
                }

                None
            }
            // Part of #1402 Phase 2: Handle linear expressions like (+ x k), (- x k), (* k x)
            ChcExpr::Op(op, _)
                if matches!(op, ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Neg)
                    && Self::is_linear_int_expr(expr) =>
            {
                // For linear expressions, probe candidate values similarly to variables
                let mut candidates: FxHashSet<i128> = FxHashSet::default();
                candidates.insert(0);
                candidates.insert(1);
                candidates.insert(-1);
                Self::collect_constants_from_expr(constraint, &mut candidates);
                Self::collect_constants_from_expr(expr, &mut candidates);
                let mut sorted_candidates: Vec<i128> = candidates.into_iter().collect();
                sorted_candidates.sort_by_key(|x| x.unsigned_abs());

                // Check if constraint implies expr = k for some k
                for test_val in &sorted_candidates {
                    let val_eq = ChcExpr::eq(expr.clone(), ChcExpr::Int(*test_val));
                    let query = ChcExpr::and(constraint.clone(), ChcExpr::not(val_eq));

                    self.smt.reset();
                    match self
                        .smt
                        .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                    {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            return Some(InitIntBounds::new(*test_val));
                        }
                        _ => {}
                    }
                }

                // Find bounds
                let mut lower_bound: Option<i128> = None;
                for test_val in &sorted_candidates {
                    let val_ge = ChcExpr::ge(expr.clone(), ChcExpr::Int(*test_val));
                    let query = ChcExpr::and(constraint.clone(), ChcExpr::not(val_ge));

                    self.smt.reset();
                    match self
                        .smt
                        .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                    {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            lower_bound =
                                Some(lower_bound.map_or(*test_val, |lb| lb.max(*test_val)));
                        }
                        _ => {}
                    }
                }

                let mut upper_bound: Option<i128> = None;
                for test_val in &sorted_candidates {
                    let val_le = ChcExpr::le(expr.clone(), ChcExpr::Int(*test_val));
                    let query = ChcExpr::and(constraint.clone(), ChcExpr::not(val_le));

                    self.smt.reset();
                    match self
                        .smt
                        .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                    {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            upper_bound =
                                Some(upper_bound.map_or(*test_val, |ub| ub.min(*test_val)));
                        }
                        _ => {}
                    }
                }

                if lower_bound.is_some() || upper_bound.is_some() {
                    let mut bounds = InitIntBounds::unbounded();
                    if let Some(lb) = lower_bound {
                        bounds.min = lb;
                    }
                    if let Some(ub) = upper_bound {
                        bounds.max = ub;
                    }
                    return Some(bounds);
                }

                None
            }
            _ => None,
        }
    }
}
