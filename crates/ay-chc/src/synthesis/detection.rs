// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pattern detection for structural invariant synthesis.
//!
//! Detects loop patterns (bounded increment/decrement, interval bounds)
//! from CHC transition clause structure.

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, ClauseHead, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::types::{LoopPattern, SynthesisPattern};
use super::StructuralSynthesizer;

impl<'a> StructuralSynthesizer<'a> {
    /// Detect loop patterns from problem structure.
    pub(super) fn detect_patterns(&self) -> Vec<LoopPattern> {
        let mut patterns = Vec::new();

        // Precompute canonical vars and init values for Int-only predicates.
        let mut canonical_vars_by_pred: FxHashMap<PredicateId, Vec<ChcVar>> = FxHashMap::default();
        let mut init_values_by_pred: FxHashMap<PredicateId, FxHashMap<String, i128>> =
            FxHashMap::default();

        for pred in self.problem.predicates() {
            // Structural synthesis only handles Int arguments - bounds like x <= N
            // don't make sense for Bool or other sorts.
            if !pred.arg_sorts.iter().all(|s| matches!(s, ChcSort::Int)) {
                continue;
            }

            // Get the canonical variable names for this predicate using actual sorts.
            let canonical_vars: Vec<ChcVar> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                .collect();
            let init_values = self.extract_init_values(pred.id, &canonical_vars);

            canonical_vars_by_pred.insert(pred.id, canonical_vars);
            init_values_by_pred.insert(pred.id, init_values);
        }

        // Analyze transition clause for updates and guards
        for transition in self.problem.transitions() {
            // Structural synthesis patterns currently require linear transitions:
            // one body predicate and a predicate head.
            if transition.body.predicates.len() != 1 {
                continue;
            }

            let [(body_pred, _)] = transition.body.predicates.as_slice() else {
                continue;
            };
            let ClauseHead::Predicate(head_pred, _) = &transition.head else {
                continue;
            };

            let Some(body_canonical_vars) = canonical_vars_by_pred.get(body_pred) else {
                continue;
            };
            let Some(head_canonical_vars) = canonical_vars_by_pred.get(head_pred) else {
                continue;
            };
            let Some(head_init_values) = init_values_by_pred.get(head_pred) else {
                continue;
            };

            if let Some(pattern) = self.analyze_transition(
                transition,
                *body_pred,
                body_canonical_vars,
                *head_pred,
                head_canonical_vars,
                head_init_values,
            ) {
                patterns.push(pattern);
            }
        }

        patterns
    }

    /// Extract initial values from fact clauses.
    pub(super) fn extract_init_values(
        &self,
        pred_id: PredicateId,
        canonical_vars: &[ChcVar],
    ) -> FxHashMap<String, i128> {
        let mut init_values = FxHashMap::default();

        for fact in self.problem.facts() {
            if let ClauseHead::Predicate(head_pred, args) = &fact.head {
                if *head_pred != pred_id {
                    continue;
                }

                // Check constraint for direct equality assignments
                if let Some(constraint) = &fact.body.constraint {
                    Self::extract_equalities_from_constraint(
                        constraint,
                        args,
                        canonical_vars,
                        &mut init_values,
                    );
                }

                // Also check if head args are constant (handles Op(Neg,[Int(n)]) too)
                for (i, arg) in args.iter().enumerate() {
                    if let Some(v) = arg.as_i128() {
                        if i < canonical_vars.len() {
                            init_values.insert(canonical_vars[i].name.clone(), v);
                        }
                    }
                }
            }
        }

        init_values
    }

    /// Extract equality constraints from a formula.
    fn extract_equalities_from_constraint(
        expr: &ChcExpr,
        head_args: &[ChcExpr],
        canonical_vars: &[ChcVar],
        init_values: &mut FxHashMap<String, i128>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::extract_equalities_from_constraint(
                        arg,
                        head_args,
                        canonical_vars,
                        init_values,
                    );
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Look for patterns like (= x 0) or (= 0 x)
                // Handles Op(Neg,[Int(n)]) for negative constants via as_i128()
                let (var_expr, val) = if let Some(n) = args[1].as_i128() {
                    (args[0].as_ref(), n)
                } else if let Some(n) = args[0].as_i128() {
                    (args[1].as_ref(), n)
                } else {
                    return;
                };

                if let ChcExpr::Var(v) = var_expr {
                    // Map the variable to canonical form
                    for (i, head_arg) in head_args.iter().enumerate() {
                        if let ChcExpr::Var(head_var) = head_arg {
                            if head_var.name == v.name && i < canonical_vars.len() {
                                init_values.insert(canonical_vars[i].name.clone(), val);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// Analyze a transition clause for loop patterns.
    fn analyze_transition(
        &self,
        clause: &crate::HornClause,
        body_pred_id: PredicateId,
        body_canonical_vars: &[ChcVar],
        head_pred_id: PredicateId,
        head_canonical_vars: &[ChcVar],
        head_init_values: &FxHashMap<String, i128>,
    ) -> Option<LoopPattern> {
        // Get body and head predicate applications
        let (body_pred, body_args) = clause.body.predicates.first()?;
        if *body_pred != body_pred_id {
            return None;
        }

        let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
            return None;
        };
        if *head_pred != head_pred_id {
            return None;
        }

        // Build variable mapping from body args to canonical vars (by body predicate arity).
        // #2660: Only Var body args get mapped; expression body args (e.g., x+1)
        // can't be meaningfully mapped to a single canonical var, and identity
        // mapping would pollute the map. Pattern detection already returns None
        // for non-Var body args.
        let mut var_map: FxHashMap<String, String> = FxHashMap::default();
        for (i, arg) in body_args.iter().enumerate() {
            if i >= body_canonical_vars.len() {
                continue;
            }
            if let ChcExpr::Var(v) = arg {
                var_map.insert(v.name.clone(), body_canonical_vars[i].name.clone());
            }
        }

        // Analyze updates (head_args vs body_args) and synthesize an invariant for the HEAD predicate.
        for (i, (head_arg, body_arg)) in head_args.iter().zip(body_args.iter()).enumerate() {
            if i >= head_canonical_vars.len() {
                continue;
            }

            let canonical_var = &head_canonical_vars[i];

            // Check for x' = x + K pattern
            if let Some(stride) = self.detect_additive_update(head_arg, body_arg, &var_map) {
                // Extract bounds from guard
                let (lower, upper) =
                    self.extract_bounds_from_guard(&clause.body.constraint, body_arg, &var_map);

                let pattern = if stride > 0 && upper.is_some() {
                    SynthesisPattern::BoundedIncrement
                } else if stride < 0 && lower.is_some() {
                    SynthesisPattern::BoundedDecrement
                } else {
                    SynthesisPattern::IntervalBounds
                };

                return Some(LoopPattern {
                    pred_id: head_pred_id,
                    var_index: i,
                    var: canonical_var.clone(),
                    stride,
                    upper_bound: upper,
                    lower_bound: lower,
                    init_value: head_init_values.get(&canonical_var.name).copied(),
                    pattern,
                });
            }
        }

        None
    }

    /// Detect additive update pattern: x' = x + K.
    fn detect_additive_update(
        &self,
        head_arg: &ChcExpr,
        body_arg: &ChcExpr,
        var_map: &FxHashMap<String, String>,
    ) -> Option<i128> {
        // head_arg should be Add(body_var, constant) or Sub(body_var, constant)
        match head_arg {
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                // Check (+ x K) or (+ K x)
                let (var_arg, const_arg) = if matches!(args[1].as_ref(), ChcExpr::Int(_)) {
                    (args[0].as_ref(), args[1].as_ref())
                } else if matches!(args[0].as_ref(), ChcExpr::Int(_)) {
                    (args[1].as_ref(), args[0].as_ref())
                } else {
                    return None;
                };

                if self.expr_matches_var(var_arg, body_arg, var_map) {
                    if let ChcExpr::Int(k) = const_arg {
                        return Some(*k);
                    }
                }
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                // Check (- x K)
                if let (var_arg, ChcExpr::Int(k)) = (args[0].as_ref(), args[1].as_ref()) {
                    if self.expr_matches_var(var_arg, body_arg, var_map) {
                        return k.checked_neg();
                    }
                }
            }
            _ => {}
        }
        None
    }

    /// Check if an expression matches a variable (with renaming).
    pub(super) fn expr_matches_var(
        &self,
        expr: &ChcExpr,
        body_arg: &ChcExpr,
        var_map: &FxHashMap<String, String>,
    ) -> bool {
        if let (ChcExpr::Var(e_var), ChcExpr::Var(b_var)) = (expr, body_arg) {
            // Direct match
            if e_var.name == b_var.name {
                return true;
            }
            // Match via var_map
            if let Some(canonical) = var_map.get(&e_var.name) {
                if let Some(body_canonical) = var_map.get(&b_var.name) {
                    return canonical == body_canonical;
                }
            }
        }
        false
    }

    /// Extract bounds from guard constraint.
    pub(super) fn extract_bounds_from_guard(
        &self,
        constraint: &Option<ChcExpr>,
        body_arg: &ChcExpr,
        var_map: &FxHashMap<String, String>,
    ) -> (Option<i128>, Option<i128>) {
        let mut lower = None;
        let mut upper = None;

        let Some(constraint) = constraint else {
            return (lower, upper);
        };

        self.extract_bounds_recursive(constraint, body_arg, var_map, &mut lower, &mut upper);
        (lower, upper)
    }

    fn extract_bounds_recursive(
        &self,
        expr: &ChcExpr,
        body_arg: &ChcExpr,
        var_map: &FxHashMap<String, String>,
        lower: &mut Option<i128>,
        upper: &mut Option<i128>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    self.extract_bounds_recursive(arg, body_arg, var_map, lower, upper);
                }
            }
            // x < N or x <= N gives upper bound
            ChcExpr::Op(ChcOp::Lt | ChcOp::Le, args) if args.len() == 2 => {
                // Check x < N pattern
                if let (var_expr, ChcExpr::Int(bound)) = (args[0].as_ref(), args[1].as_ref()) {
                    if self.expr_matches_var(var_expr, body_arg, var_map) {
                        // i128-lockstep: checked adjust; ignore the bound on overflow.
                        let u = if matches!(expr, ChcExpr::Op(ChcOp::Lt, _)) {
                            bound.checked_sub(1)
                        } else {
                            Some(*bound)
                        };
                        if let Some(u) = u {
                            *upper = Some(upper.map_or(u, |prev| prev.min(u)));
                        }
                    }
                }
                // Check N < x pattern (flipped: Lt(N, x) means N < x, i.e., x > N -> lower bound)
                if let (ChcExpr::Int(bound), var_expr) = (args[0].as_ref(), args[1].as_ref()) {
                    if self.expr_matches_var(var_expr, body_arg, var_map) {
                        // N < x means x > N, giving lower bound
                        // i128-lockstep: checked adjust; ignore the bound on overflow.
                        let l = if matches!(expr, ChcExpr::Op(ChcOp::Lt, _)) {
                            bound.checked_add(1)
                        } else {
                            Some(*bound)
                        };
                        if let Some(l) = l {
                            *lower = Some(lower.map_or(l, |prev| prev.max(l)));
                        }
                    }
                }
            }
            // x > N or x >= N gives lower bound
            ChcExpr::Op(ChcOp::Gt | ChcOp::Ge, args) if args.len() == 2 => {
                // Check x > N pattern
                if let (var_expr, ChcExpr::Int(bound)) = (args[0].as_ref(), args[1].as_ref()) {
                    if self.expr_matches_var(var_expr, body_arg, var_map) {
                        // i128-lockstep: checked adjust; ignore the bound on overflow.
                        let l = if matches!(expr, ChcExpr::Op(ChcOp::Gt, _)) {
                            bound.checked_add(1)
                        } else {
                            Some(*bound)
                        };
                        if let Some(l) = l {
                            *lower = Some(lower.map_or(l, |prev| prev.max(l)));
                        }
                    }
                }
                // Check N > x pattern (flipped: Gt(N, x) means N > x, i.e., x < N -> upper bound)
                if let (ChcExpr::Int(bound), var_expr) = (args[0].as_ref(), args[1].as_ref()) {
                    if self.expr_matches_var(var_expr, body_arg, var_map) {
                        // N > x means x < N, giving upper bound
                        // i128-lockstep: checked adjust; ignore the bound on overflow.
                        let u = if matches!(expr, ChcExpr::Op(ChcOp::Gt, _)) {
                            bound.checked_sub(1)
                        } else {
                            Some(*bound)
                        };
                        if let Some(u) = u {
                            *upper = Some(upper.map_or(u, |prev| prev.min(u)));
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
