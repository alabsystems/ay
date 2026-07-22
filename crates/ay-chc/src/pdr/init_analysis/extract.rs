// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Init value extraction and equality propagation.
//!
//! Contains `extract_init_values` (constraint → bounds), expression equality
//! propagation, linear expression evaluation, and variable-variable equality
//! extraction from init constraints.

use crate::{ChcExpr, ChcOp, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::super::config::InitIntBounds;
use super::super::solver::PdrSolver;

fn exact_literal_value(expr: &ChcExpr) -> Option<i128> {
    match expr {
        ChcExpr::Int(n) => Some(*n),
        ChcExpr::BitVec(bits, _) => i128::try_from(*bits).ok(),
        _ => None,
    }
}

impl PdrSolver {
    /// Extract constant values and bounds from init constraints (equalities and inequalities)
    pub(in crate::pdr) fn extract_init_values(
        expr: &ChcExpr,
        var_map: &FxHashMap<String, String>,
        values: &mut FxHashMap<String, InitIntBounds>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::extract_init_values(arg, var_map, values);
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Try var = const or const = var
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        if let Some(n) = exact_literal_value(args[1].as_ref()) {
                            values
                                .entry(canon_name.clone())
                                .and_modify(|b| b.update(n))
                                .or_insert_with(|| InitIntBounds::new(n));
                        }
                    }
                }
                if let ChcExpr::Var(v) = args[1].as_ref() {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        if let Some(n) = exact_literal_value(args[0].as_ref()) {
                            values
                                .entry(canon_name.clone())
                                .and_modify(|b| b.update(n))
                                .or_insert_with(|| InitIntBounds::new(n));
                        }
                    }
                }
            }
            // Handle (>= var const) → lower bound const
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref()) {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        values
                            .entry(canon_name.clone())
                            .and_modify(|b| b.update_lower(*n))
                            .or_insert_with(|| {
                                let mut b = InitIntBounds::unbounded();
                                b.update_lower(*n);
                                b
                            });
                    }
                }
                // (>= const var) means const >= var, i.e., var <= const → upper bound
                if let (ChcExpr::Int(n), ChcExpr::Var(v)) = (args[0].as_ref(), args[1].as_ref()) {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        values
                            .entry(canon_name.clone())
                            .and_modify(|b| b.update_upper(*n))
                            .or_insert_with(|| {
                                let mut b = InitIntBounds::unbounded();
                                b.update_upper(*n);
                                b
                            });
                    }
                }
            }
            // Handle (> var const) → lower bound const + 1
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref()) {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        values
                            .entry(canon_name.clone())
                            .and_modify(|b| b.update_lower(n.saturating_add(1)))
                            .or_insert_with(|| {
                                let mut b = InitIntBounds::unbounded();
                                b.update_lower(n.saturating_add(1));
                                b
                            });
                    }
                }
                // (> const var) means const > var, i.e., var < const → upper bound const - 1
                if let (ChcExpr::Int(n), ChcExpr::Var(v)) = (args[0].as_ref(), args[1].as_ref()) {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        values
                            .entry(canon_name.clone())
                            .and_modify(|b| b.update_upper(n.saturating_sub(1)))
                            .or_insert_with(|| {
                                let mut b = InitIntBounds::unbounded();
                                b.update_upper(n.saturating_sub(1));
                                b
                            });
                    }
                }
            }
            // Handle (<= var const) → upper bound const
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref()) {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        values
                            .entry(canon_name.clone())
                            .and_modify(|b| b.update_upper(*n))
                            .or_insert_with(|| {
                                let mut b = InitIntBounds::unbounded();
                                b.update_upper(*n);
                                b
                            });
                    }
                }
                // (<= const var) means const <= var, i.e., var >= const → lower bound
                if let (ChcExpr::Int(n), ChcExpr::Var(v)) = (args[0].as_ref(), args[1].as_ref()) {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        values
                            .entry(canon_name.clone())
                            .and_modify(|b| b.update_lower(*n))
                            .or_insert_with(|| {
                                let mut b = InitIntBounds::unbounded();
                                b.update_lower(*n);
                                b
                            });
                    }
                }
            }
            // Handle (< var const) → upper bound const - 1
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (args[0].as_ref(), args[1].as_ref()) {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        values
                            .entry(canon_name.clone())
                            .and_modify(|b| b.update_upper(n.saturating_sub(1)))
                            .or_insert_with(|| {
                                let mut b = InitIntBounds::unbounded();
                                b.update_upper(n.saturating_sub(1));
                                b
                            });
                    }
                }
                // (< const var) means const < var, i.e., var > const → lower bound const + 1
                if let (ChcExpr::Int(n), ChcExpr::Var(v)) = (args[0].as_ref(), args[1].as_ref()) {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        values
                            .entry(canon_name.clone())
                            .and_modify(|b| b.update_lower(n.saturating_add(1)))
                            .or_insert_with(|| {
                                let mut b = InitIntBounds::unbounded();
                                b.update_lower(n.saturating_add(1));
                                b
                            });
                    }
                }
            }
            // Handle (not (<= const var)) → var < const → upper bound const - 1
            // Handle (not (<= var const)) → var > const → lower bound const + 1
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                if let ChcExpr::Op(ChcOp::Le, inner_args) = args[0].as_ref() {
                    if inner_args.len() == 2 {
                        // not (<= const var) → var < const → upper bound const - 1
                        if let (ChcExpr::Int(n), ChcExpr::Var(v)) =
                            (inner_args[0].as_ref(), inner_args[1].as_ref())
                        {
                            if let Some(canon_name) = var_map.get(&v.name) {
                                values
                                    .entry(canon_name.clone())
                                    .and_modify(|b| b.update_upper(n.saturating_sub(1)))
                                    .or_insert_with(|| {
                                        let mut b = InitIntBounds::unbounded();
                                        b.update_upper(n.saturating_sub(1));
                                        b
                                    });
                            }
                        }
                        // not (<= var const) → var > const → lower bound const + 1
                        if let (ChcExpr::Var(v), ChcExpr::Int(n)) =
                            (inner_args[0].as_ref(), inner_args[1].as_ref())
                        {
                            if let Some(canon_name) = var_map.get(&v.name) {
                                values
                                    .entry(canon_name.clone())
                                    .and_modify(|b| b.update_lower(n.saturating_add(1)))
                                    .or_insert_with(|| {
                                        let mut b = InitIntBounds::unbounded();
                                        b.update_lower(n.saturating_add(1));
                                        b
                                    });
                            }
                        }
                    }
                }
            }
            // Handle (or (= var c1) (= var c2) ...) → bounds from union of constants
            ChcExpr::Op(ChcOp::Or, args) => {
                // Try to extract variable-constant equality patterns
                let mut var_constants: FxHashMap<String, Vec<i128>> = FxHashMap::default();
                for arg in args {
                    if let ChcExpr::Op(ChcOp::Eq, eq_args) = arg.as_ref() {
                        if eq_args.len() == 2 {
                            if let ChcExpr::Var(v) = eq_args[0].as_ref() {
                                if let Some(canon_name) = var_map.get(&v.name) {
                                    if let Some(n) = exact_literal_value(eq_args[1].as_ref()) {
                                        var_constants
                                            .entry(canon_name.clone())
                                            .or_default()
                                            .push(n);
                                    }
                                }
                            }
                            if let ChcExpr::Var(v) = eq_args[1].as_ref() {
                                if let Some(canon_name) = var_map.get(&v.name) {
                                    if let Some(n) = exact_literal_value(eq_args[0].as_ref()) {
                                        var_constants
                                            .entry(canon_name.clone())
                                            .or_default()
                                            .push(n);
                                    }
                                }
                            }
                        }
                    }
                }
                // If we found a single variable mentioned in all OR branches with constants
                for (canon_name, constants) in var_constants {
                    if constants.len() == args.len() && !constants.is_empty() {
                        // All branches are about this variable
                        let min_val = *constants.iter().min().expect("non-empty");
                        let max_val = *constants.iter().max().expect("non-empty");
                        values
                            .entry(canon_name)
                            .and_modify(|b| {
                                b.update_lower(min_val);
                                b.update_upper(max_val);
                            })
                            .or_insert_with(|| InitIntBounds {
                                min: min_val,
                                max: max_val,
                            });
                    }
                }
            }
            _ => {}
        }
    }

    /// Propagate expression-based equalities using known init values (#1472).
    ///
    /// For equalities of the form `var = expr` where `expr` contains variables
    /// with known exact values, evaluate `expr` and add the result as a bound
    /// for `var`.
    ///
    /// Example: Given `(= C (+ A (* (- 1) B)))` with `A=1, B=0`, computes `C=1`.
    pub(in crate::pdr) fn propagate_expr_equalities(
        expr: &ChcExpr,
        var_map: &FxHashMap<String, String>,
        values: &mut FxHashMap<String, InitIntBounds>,
    ) {
        // Build reverse map: canonical name -> original variable name
        let mut reverse_map: FxHashMap<String, String> = FxHashMap::default();
        for (orig, canon) in var_map {
            reverse_map.insert(canon.clone(), orig.clone());
        }

        // Build known values map: original variable name -> value
        let mut known_values: FxHashMap<String, i128> = FxHashMap::default();
        for (canon_name, bounds) in values.iter() {
            if bounds.min == bounds.max {
                if let Some(orig_name) = reverse_map.get(canon_name) {
                    known_values.insert(orig_name.clone(), bounds.min);
                }
            }
        }

        if known_values.is_empty() {
            return;
        }

        Self::propagate_expr_equalities_inner(expr, var_map, &known_values, values);
    }

    fn propagate_expr_equalities_inner(
        expr: &ChcExpr,
        var_map: &FxHashMap<String, String>,
        known_values: &FxHashMap<String, i128>,
        values: &mut FxHashMap<String, InitIntBounds>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::propagate_expr_equalities_inner(arg, var_map, known_values, values);
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Try var = expr pattern
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        // Skip if already have exact value
                        if let Some(bounds) = values.get(canon_name) {
                            if bounds.min == bounds.max {
                                return;
                            }
                        }
                        // Try to evaluate RHS with known values
                        if let Some(val) = Self::eval_linear_expr(&args[1], known_values) {
                            values.insert(canon_name.clone(), InitIntBounds::new(val));
                        }
                    }
                }
                // Try expr = var pattern
                if let ChcExpr::Var(v) = args[1].as_ref() {
                    if let Some(canon_name) = var_map.get(&v.name) {
                        if let Some(bounds) = values.get(canon_name) {
                            if bounds.min == bounds.max {
                                return;
                            }
                        }
                        if let Some(val) = Self::eval_linear_expr(&args[0], known_values) {
                            values.insert(canon_name.clone(), InitIntBounds::new(val));
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// Evaluate a linear arithmetic expression using known variable values.
    /// Returns None if any variable is unknown or the expression is non-linear.
    pub(in crate::pdr) fn eval_linear_expr(
        expr: &ChcExpr,
        known_values: &FxHashMap<String, i128>,
    ) -> Option<i128> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Int(n) => Some(*n),
            ChcExpr::Var(v) => known_values.get(&v.name).copied(),
            ChcExpr::Op(ChcOp::Add, args) => {
                let mut sum: i128 = 0;
                for arg in args {
                    sum = sum.checked_add(Self::eval_linear_expr(arg, known_values)?)?;
                }
                Some(sum)
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                let lhs = Self::eval_linear_expr(&args[0], known_values)?;
                let rhs = Self::eval_linear_expr(&args[1], known_values)?;
                lhs.checked_sub(rhs)
            }
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                let lhs = Self::eval_linear_expr(&args[0], known_values)?;
                let rhs = Self::eval_linear_expr(&args[1], known_values)?;
                lhs.checked_mul(rhs)
            }
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                let val = Self::eval_linear_expr(&args[0], known_values)?;
                val.checked_neg()
            }
            _ => None,
        })
    }

    /// Extract variable-to-variable equalities from init constraints.
    ///
    /// Returns a set of (canonical_var_i_name, canonical_var_j_name) pairs where
    /// the init constraint contains `var_i = var_j`.
    pub(in crate::pdr) fn get_init_var_var_equalities(
        &self,
        predicate: PredicateId,
    ) -> FxHashSet<(String, String)> {
        let mut equalities = FxHashSet::default();

        for fact in self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(predicate))
        {
            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            let canonical_vars = match self.canonical_vars(predicate) {
                Some(v) => v,
                None => continue,
            };

            if head_args.len() != canonical_vars.len() {
                continue;
            }

            // Map original variable names to canonical names.
            // #2660: Only Var head args get mapped; expression head args (e.g., x+1)
            // can't be meaningfully mapped to a single canonical var.
            let mut var_map: FxHashMap<String, String> = FxHashMap::default();
            for (arg, canon) in head_args.iter().zip(canonical_vars.iter()) {
                if let ChcExpr::Var(v) = arg {
                    var_map.insert(v.name.clone(), canon.name.clone());
                }
            }

            // Extract var = var equalities
            Self::extract_var_var_equalities_from_constraint(
                &constraint,
                &var_map,
                &mut equalities,
            );
        }

        equalities
    }

    /// Recursively extract var=var equalities from a constraint formula.
    fn extract_var_var_equalities_from_constraint(
        expr: &ChcExpr,
        var_map: &FxHashMap<String, String>,
        equalities: &mut FxHashSet<(String, String)>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::extract_var_var_equalities_from_constraint(arg, var_map, equalities);
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check for var = var
                if let (ChcExpr::Var(v1), ChcExpr::Var(v2)) = (args[0].as_ref(), args[1].as_ref()) {
                    if let (Some(canon1), Some(canon2)) =
                        (var_map.get(&v1.name), var_map.get(&v2.name))
                    {
                        if canon1 != canon2 {
                            // Store in canonical order to avoid duplicates
                            let (a, b) = if canon1 < canon2 {
                                (canon1.clone(), canon2.clone())
                            } else {
                                (canon2.clone(), canon1.clone())
                            };
                            equalities.insert((a, b));
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// Extract a variable and constant from an equality conjunct (v = c).
    /// Delegated to generalization module.
    pub(in crate::pdr) fn extract_equality(expr: &ChcExpr) -> Option<(ChcVar, i128)> {
        crate::pdr::generalization::extract_equality(expr)
    }
}
