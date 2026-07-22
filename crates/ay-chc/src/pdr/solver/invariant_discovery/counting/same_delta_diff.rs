// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Same-delta constant-difference invariant discovery.
//!
//! When two variables have the same self-loop increment (delta), their
//! difference is preserved across transitions. If the initial difference
//! can be expressed as a linear function of constant (delta=0) variables,
//! we emit that as an invariant.
//!
//! Example: s_mutants_16 has A (delta=1, init=0) and B (delta=1, init=3*E).
//! Since delta(A) = delta(B) = 1, B - A = 3*E - 0 = 3*E is invariant.

use super::*;

impl PdrSolver {
    /// Discover invariants from pairs of variables with equal self-loop deltas.
    ///
    /// For each predicate with fact clauses, finds pairs (A, B) where:
    /// 1. Both have the same constant self-loop increment
    /// 2. The initial difference B_init - A_init can be expressed in terms of
    ///    constant (delta=0) variables
    ///
    /// Emits invariant: B - A = init_diff_expr
    pub(in crate::pdr::solver) fn discover_same_delta_difference_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Extract self-loop deltas for each variable
            let deltas = self.extract_self_loop_deltas(pred.id, &canonical_vars);
            if deltas.is_empty() {
                continue;
            }

            // Find constant (delta=0) variables
            let constant_var_indices: FxHashSet<usize> = deltas
                .iter()
                .filter(|(_, d)| *d == 0)
                .map(|(idx, _)| *idx)
                .collect();

            // Get init expressions for all variables
            let init_values = self.get_init_values(pred.id);

            // For each pair with same nonzero delta, check if difference is expressible
            let int_vars_with_delta: Vec<(usize, i128)> = deltas
                .iter()
                .filter(|(idx, _)| matches!(canonical_vars[*idx].sort, ChcSort::Int))
                .copied()
                .collect();

            let mut candidates: Vec<(PredicateId, ChcExpr)> = Vec::new();

            for i in 0..int_vars_with_delta.len() {
                for j in (i + 1)..int_vars_with_delta.len() {
                    let (idx_a, delta_a) = int_vars_with_delta[i];
                    let (idx_b, delta_b) = int_vars_with_delta[j];

                    if delta_a != delta_b {
                        continue;
                    }

                    let var_a = &canonical_vars[idx_a];
                    let var_b = &canonical_vars[idx_b];

                    // Get initial values/expressions
                    let init_a = init_values.get(&var_a.name);
                    let init_b = init_values.get(&var_b.name);

                    // Case 1: Both have known constant init values
                    if let (Some(bounds_a), Some(bounds_b)) = (init_a, init_b) {
                        if bounds_a.min == bounds_a.max && bounds_b.min == bounds_b.max {
                            let diff = bounds_b.min - bounds_a.min;
                            if diff != 0 {
                                // B - A = diff (constant)
                                let invariant = ChcExpr::eq(
                                    ChcExpr::sub(
                                        ChcExpr::var(var_b.clone()),
                                        ChcExpr::var(var_a.clone()),
                                    ),
                                    ChcExpr::Int(diff),
                                );
                                candidates.push((pred.id, invariant));
                            }
                            continue;
                        }
                    }

                    // Case 2: One has a constant init, the other has an expression
                    // involving constant variables. Try to express difference.
                    let init_expr_a = self.get_init_expression_for_var(pred.id, idx_a);
                    let init_expr_b = self.get_init_expression_for_var(pred.id, idx_b);

                    if let (Some(expr_a), Some(expr_b)) = (&init_expr_a, &init_expr_b) {
                        // Check if the difference involves only constant variables
                        let diff_expr = self.try_build_init_difference(
                            pred.id,
                            expr_b,
                            expr_a,
                            &canonical_vars,
                            &constant_var_indices,
                        );

                        if let Some(diff) = diff_expr {
                            let invariant = ChcExpr::eq(
                                ChcExpr::sub(
                                    ChcExpr::var(var_b.clone()),
                                    ChcExpr::var(var_a.clone()),
                                ),
                                diff.clone(),
                            );

                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered same-delta diff invariant for pred {}: {} - {} = {}",
                                    pred.id.index(),
                                    var_b.name,
                                    var_a.name,
                                    diff,
                                );
                            }

                            candidates.push((pred.id, invariant));
                        }
                    }
                }
            }

            for (pred_id, formula) in candidates {
                self.add_discovered_invariant_algebraic(pred_id, formula, 1);
            }
        }
    }

    /// Extract constant self-loop deltas for each variable.
    /// Returns Vec<(var_index, delta)> for variables with a single constant delta
    /// across ALL self-loop transitions.
    fn extract_self_loop_deltas(
        &self,
        predicate: PredicateId,
        canonical_vars: &[ChcVar],
    ) -> Vec<(usize, i128)> {
        let mut result = Vec::new();

        for (idx, var) in canonical_vars.iter().enumerate() {
            if !matches!(var.sort, ChcSort::Int) {
                continue;
            }

            let mut all_deltas: Vec<i128> = Vec::new();
            let mut consistent = true;

            for clause in self.problem.clauses_defining(predicate) {
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (body_pred, body_args) = &clause.body.predicates[0];
                if *body_pred != predicate {
                    continue;
                }
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if head_args.len() != canonical_vars.len()
                    || body_args.len() != canonical_vars.len()
                {
                    continue;
                }

                let body_val = &body_args[idx];
                let head_val = &head_args[idx];

                // Try direct offset
                if let Some(offset) = Self::extract_simple_offset(body_val, head_val) {
                    all_deltas.push(offset);
                    continue;
                }

                // Try constraint-defined offset
                if let (ChcExpr::Var(pre_v), ChcExpr::Var(post_v)) = (body_val, head_val) {
                    if let Some(constr) = clause.body.constraint.as_ref() {
                        if let Some(offset) =
                            Self::find_offset_in_constraint(constr, &pre_v.name, &post_v.name)
                        {
                            all_deltas.push(offset);
                            continue;
                        }
                    }
                }

                // Check if variable is unchanged (delta = 0)
                if body_val == head_val {
                    all_deltas.push(0);
                    continue;
                }
                if let (ChcExpr::Var(pre_v), ChcExpr::Var(post_v)) = (body_val, head_val) {
                    if let Some(constr) = clause.body.constraint.as_ref() {
                        if Self::constraint_implies_equality(constr, &pre_v.name, &post_v.name) {
                            all_deltas.push(0);
                            continue;
                        }
                    }
                }

                consistent = false;
                break;
            }

            if consistent && !all_deltas.is_empty() {
                // All deltas must be the same
                let first = all_deltas[0];
                if all_deltas.iter().all(|d| *d == first) {
                    result.push((idx, first));
                }
            }
        }

        result
    }

    /// Check if a constraint implies pre_var = post_var (equality).
    fn constraint_implies_equality(constraint: &ChcExpr, pre_var: &str, post_var: &str) -> bool {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => args
                .iter()
                .any(|a| Self::constraint_implies_equality(a, pre_var, post_var)),
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let (lhs, rhs) = (&args[0], &args[1]);
                (matches!(lhs.as_ref(), ChcExpr::Var(v) if v.name == post_var)
                    && matches!(rhs.as_ref(), ChcExpr::Var(v) if v.name == pre_var))
                    || (matches!(lhs.as_ref(), ChcExpr::Var(v) if v.name == pre_var)
                        && matches!(rhs.as_ref(), ChcExpr::Var(v) if v.name == post_var))
            }
            _ => false,
        }
    }

    /// Try to build an expression for (expr_b - expr_a) that only involves
    /// constant variables (delta=0) and integer constants.
    ///
    /// Returns Some(diff_expr) in terms of canonical variables if successful.
    fn try_build_init_difference(
        &self,
        predicate: PredicateId,
        expr_b: &ChcExpr,
        expr_a: &ChcExpr,
        canonical_vars: &[ChcVar],
        constant_var_indices: &FxHashSet<usize>,
    ) -> Option<ChcExpr> {
        // Build mapping from fact clause vars to canonical vars
        let var_to_canonical = self.build_fact_var_to_canonical_map(predicate, canonical_vars)?;

        // Simple case: expr_a is Int(0) and expr_b involves only constant vars
        let simplified_a = Self::simplify_init_expr(expr_a, &var_to_canonical);
        let simplified_b = Self::simplify_init_expr(expr_b, &var_to_canonical);

        // Check if both sides only reference constant variables
        let a_vars = simplified_a.vars();
        let b_vars = simplified_b.vars();

        let all_constant = a_vars.iter().chain(b_vars.iter()).all(|v| {
            canonical_vars
                .iter()
                .position(|cv| cv.name == v.name)
                .map(|idx| constant_var_indices.contains(&idx))
                .unwrap_or(false)
        });

        if !all_constant {
            return None;
        }

        // Build difference expression
        match (&simplified_a, &simplified_b) {
            (ChcExpr::Int(0), _) => Some(simplified_b),
            (ChcExpr::Int(a), ChcExpr::Int(b)) => Some(ChcExpr::Int(b - a)),
            (_, ChcExpr::Int(0)) => Some(ChcExpr::neg(simplified_a)),
            _ => Some(ChcExpr::sub(simplified_b, simplified_a)),
        }
    }

    /// Build mapping from fact clause variable names to canonical variable names.
    fn build_fact_var_to_canonical_map(
        &self,
        predicate: PredicateId,
        canonical_vars: &[ChcVar],
    ) -> Option<FxHashMap<String, String>> {
        let mut map = FxHashMap::default();
        for fact in self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(predicate))
        {
            let head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };
            if head_args.len() != canonical_vars.len() {
                continue;
            }
            for (arg, canon) in head_args.iter().zip(canonical_vars.iter()) {
                if let ChcExpr::Var(v) = arg {
                    map.insert(v.name.clone(), canon.name.clone());
                }
            }
            return Some(map);
        }
        None
    }

    /// Substitute fact clause variables with canonical variable names in an init expression.
    fn simplify_init_expr(expr: &ChcExpr, var_to_canonical: &FxHashMap<String, String>) -> ChcExpr {
        match expr {
            ChcExpr::Var(v) => {
                if let Some(canonical_name) = var_to_canonical.get(&v.name) {
                    ChcExpr::var(ChcVar::new(canonical_name.clone(), v.sort.clone()))
                } else {
                    expr.clone()
                }
            }
            ChcExpr::Int(_) | ChcExpr::Bool(_) | ChcExpr::Real(_, _) => expr.clone(),
            ChcExpr::Op(op, args) => {
                let new_args: Vec<std::sync::Arc<ChcExpr>> = args
                    .iter()
                    .map(|a| std::sync::Arc::new(Self::simplify_init_expr(a, var_to_canonical)))
                    .collect();
                ChcExpr::Op(*op, new_args)
            }
            _ => expr.clone(),
        }
    }
}
