// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Init analysis for PDR solver.
//!
//! This module contains methods for extracting initial value bounds from fact clauses.
//! Used by the invariant discovery system to constrain variable ranges based on
//! init constraints.

mod extract;
mod init_only;

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "../init_analysis_tests.rs"]
mod tests;

use std::sync::Arc;

use crate::expr::walk_comparison_bounds;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::config::InitIntBounds;
use super::solver::PdrSolver;
use super::types::BoundType;

/// Extract comparison bounds from an expression using shared traversal (#3786).
pub(super) fn extract_bounds_recursive(
    expr: &ChcExpr,
    bounds: &mut Vec<(ChcVar, BoundType, i128)>,
) {
    walk_comparison_bounds(expr, true, true, &mut |left, op, right| {
        // Match Var op Int
        if let (ChcExpr::Var(v), ChcExpr::Int(n)) = (left, right) {
            let bt = match op {
                ChcOp::Le => BoundType::Le,
                ChcOp::Lt => BoundType::Lt,
                ChcOp::Ge => BoundType::Ge,
                ChcOp::Gt => BoundType::Gt,
                _ => return,
            };
            bounds.push((v.clone(), bt, *n));
        }
        // Match Int op Var (flipped direction)
        if let (ChcExpr::Int(n), ChcExpr::Var(v)) = (left, right) {
            let bt = match op {
                ChcOp::Le => BoundType::Ge, // n <= x means x >= n
                ChcOp::Lt => BoundType::Gt, // n < x means x > n
                ChcOp::Ge => BoundType::Le, // n >= x means x <= n
                ChcOp::Gt => BoundType::Lt, // n > x means x < n
                _ => return,
            };
            bounds.push((v.clone(), bt, *n));
        }
    });
}

const MAX_INIT_ONLY_VALUE_CACHE_ENTRIES: usize = 25_000;

#[inline]
fn bounded_insert_init_only_value_cache_with_cap(
    cache: &mut FxHashMap<(PredicateId, String, i128), (u64, bool)>,
    key: (PredicateId, String, i128),
    value: (u64, bool),
    cap: usize,
) {
    if cache.len() >= cap && !cache.contains_key(&key) {
        cache.clear();
    }
    cache.insert(key, value);
}

#[inline]
pub(super) fn bounded_insert_init_only_value_cache(
    cache: &mut FxHashMap<(PredicateId, String, i128), (u64, bool)>,
    key: (PredicateId, String, i128),
    value: (u64, bool),
) {
    bounded_insert_init_only_value_cache_with_cap(
        cache,
        key,
        value,
        MAX_INIT_ONLY_VALUE_CACHE_ENTRIES,
    );
}

impl PdrSolver {
    /// Extract init values for a predicate from fact clauses
    /// Returns a map from variable name to its (min,max) init bounds across all facts
    ///
    /// For predicates without direct fact clauses, this propagates init bounds from
    /// source predicates through rules of the form: P_source(...) => P_target(...)
    pub(in crate::pdr) fn get_init_values(
        &self,
        predicate: PredicateId,
    ) -> FxHashMap<String, InitIntBounds> {
        // Use cached values to avoid infinite recursion and repeated computation
        self.get_init_values_cached(predicate, &mut FxHashSet::default())
    }

    /// Internal helper for get_init_values with cycle detection
    fn get_init_values_cached(
        &self,
        predicate: PredicateId,
        visited: &mut FxHashSet<PredicateId>,
    ) -> FxHashMap<String, InitIntBounds> {
        // Prevent infinite recursion
        if visited.contains(&predicate) {
            return FxHashMap::default();
        }
        visited.insert(predicate);

        let mut values = FxHashMap::default();

        // Step 1: Look for direct fact clauses
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

            // Get canonical variables for this predicate
            let canonical_vars = match self.canonical_vars(predicate) {
                Some(v) => v,
                None => continue,
            };

            if head_args.len() != canonical_vars.len() {
                continue;
            }

            // Extract values from equality constraints in the init formula
            // and map them to canonical variable names.
            // #2660: Only Var head args get mapped; expression head args (e.g., x+1)
            // can't be meaningfully mapped to a single canonical var.
            let mut var_map: FxHashMap<String, String> = FxHashMap::default();
            for (arg, canon) in head_args.iter().zip(canonical_vars.iter()) {
                match arg {
                    ChcExpr::Var(v) => {
                        var_map.insert(v.name.clone(), canon.name.clone());
                    }
                    // When head arg is a constant integer like (Inv 0 1),
                    // we know the exact init value for this canonical var.
                    ChcExpr::Int(val) if matches!(canon.sort, ChcSort::Int) => {
                        values
                            .entry(canon.name.clone())
                            .and_modify(|b: &mut InitIntBounds| b.update(*val))
                            .or_insert_with(|| InitIntBounds::new(*val));
                    }
                    ChcExpr::BitVec(val, _) if matches!(canon.sort, ChcSort::BitVec(_)) => {
                        if let Ok(val) = i128::try_from(*val) {
                            values
                                .entry(canon.name.clone())
                                .and_modify(|b: &mut InitIntBounds| b.update(val))
                                .or_insert_with(|| InitIntBounds::new(val));
                        }
                    }
                    _ => {}
                }
            }

            Self::extract_init_values(&constraint, &var_map, &mut values);

            // Step 1b (#1472): Evaluate expression-based equalities
            // e.g., (= C (+ A (* (- 1) B))) with A=1, B=0 gives C=1
            Self::propagate_expr_equalities(&constraint, &var_map, &mut values);
        }

        // If we found direct facts, use those
        if !values.is_empty() {
            return values;
        }

        // Step 2: Propagate init bounds from source predicates through rules
        // Look for rules of the form: P_source(x1,...,xn) ∧ constraint => P_target(y1,...,yn)
        // where P_target is our predicate and P_source has init bounds
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses (already handled) and query clauses
            if clause.body.predicates.is_empty() {
                continue;
            }

            // For now, only handle simple rules with exactly one body predicate
            // More complex rules (hyperedges) would need more sophisticated handling
            if clause.body.predicates.len() != 1 {
                continue;
            }

            let (source_pred, source_args) = &clause.body.predicates[0];
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            // Get init bounds for the source predicate (recursive)
            let source_bounds = self.get_init_values_cached(*source_pred, visited);
            if source_bounds.is_empty() {
                continue;
            }

            // Get canonical variables for source and target predicates
            let source_canonical = match self.canonical_vars(*source_pred) {
                Some(v) => v,
                None => continue,
            };
            let target_canonical = match self.canonical_vars(predicate) {
                Some(v) => v,
                None => continue,
            };

            if source_args.len() != source_canonical.len()
                || head_args.len() != target_canonical.len()
            {
                continue;
            }

            // For each source arg that has init bounds, check if the head arg is the same variable
            // If so, propagate the bounds to the target
            for (source_arg, source_canon) in source_args.iter().zip(source_canonical.iter()) {
                if let ChcExpr::Var(source_var) = source_arg {
                    if let Some(bounds) = source_bounds.get(&source_canon.name) {
                        // Find if this variable appears in head args
                        for (head_arg, target_canon) in
                            head_args.iter().zip(target_canonical.iter())
                        {
                            if let ChcExpr::Var(head_var) = head_arg {
                                if head_var.name == source_var.name {
                                    // Same variable flows from source to target
                                    values
                                        .entry(target_canon.name.clone())
                                        .and_modify(|b| {
                                            b.min = b.min.min(bounds.min);
                                            b.max = b.max.max(bounds.max);
                                        })
                                        .or_insert(*bounds);
                                }
                            }
                        }
                    }
                }
            }

            // NEW: Handle computed expressions in head arguments
            // After relational encoding normalization, head args may be expressions like (+ 128 A)
            // rather than just variables. Compute bounds for these expressions.
            {
                // Build a map from body variable names to their source bounds
                let mut body_var_bounds: FxHashMap<String, InitIntBounds> = FxHashMap::default();
                for (source_arg, source_canon) in source_args.iter().zip(source_canonical.iter()) {
                    if let ChcExpr::Var(source_var) = source_arg {
                        if let Some(bounds) = source_bounds.get(&source_canon.name) {
                            body_var_bounds.insert(source_var.name.clone(), *bounds);
                        }
                    }
                }

                // For each head arg that is NOT a simple variable, try to compute bounds
                for (head_arg, target_canon) in head_args.iter().zip(target_canonical.iter()) {
                    // Skip if already has bounds
                    if values.contains_key(&target_canon.name) {
                        continue;
                    }

                    // Skip simple variables (handled by earlier code)
                    if matches!(head_arg, ChcExpr::Var(_)) {
                        continue;
                    }

                    // Try to compute bounds for the expression
                    if let Some(computed_bounds) =
                        Self::compute_bounds_for_expr(head_arg, &body_var_bounds)
                    {
                        values.insert(target_canon.name.clone(), computed_bounds);
                    }
                }

                // NEW: Extract bounds from transition constraint equalities
                // For patterns like (= C B) where C is a head variable and B is a body variable,
                // or (= D 0) where D is a head variable and 0 is a constant
                if let Some(constraint) = &clause.body.constraint {
                    // Build map from head variable names to their canonical names
                    let mut head_var_to_canon: FxHashMap<String, String> = FxHashMap::default();
                    for (head_arg, target_canon) in head_args.iter().zip(target_canonical.iter()) {
                        if let ChcExpr::Var(hv) = head_arg {
                            head_var_to_canon.insert(hv.name.clone(), target_canon.name.clone());
                        }
                    }

                    // Extract equalities from constraint
                    Self::extract_constraint_equalities_for_init(
                        constraint,
                        &head_var_to_canon,
                        &body_var_bounds,
                        &mut values,
                    );
                }
            }
        }

        values
    }

    /// Extract equalities from transition constraint for init value propagation
    fn extract_constraint_equalities_for_init(
        expr: &ChcExpr,
        head_var_to_canon: &FxHashMap<String, String>,
        body_var_bounds: &FxHashMap<String, InitIntBounds>,
        values: &mut FxHashMap<String, InitIntBounds>,
    ) {
        // First pass: extract lower bounds from guard constraints like (>= A 1000)
        // This tightens body_var_bounds before we process equalities
        let mut tightened_bounds = body_var_bounds.clone();
        Self::tighten_bounds_from_constraint(expr, &mut tightened_bounds);

        // Second pass: extract equalities
        Self::extract_equalities_from_constraint(
            expr,
            head_var_to_canon,
            &tightened_bounds,
            values,
        );
    }

    /// Tighten bounds based on constraint guards like (>= A 1000).
    ///
    /// Handles both `Int(n)` and `Op(Neg, [Int(n)])` representations of
    /// constants via `ChcExpr::as_i128()`.
    fn tighten_bounds_from_constraint(
        expr: &ChcExpr,
        bounds: &mut FxHashMap<String, InitIntBounds>,
    ) {
        /// Extract (var_name, constant) from a binary comparison where one side
        /// is a variable and the other is a constant. Returns (var_name, value, var_is_lhs).
        fn extract_var_const(args: &[Arc<ChcExpr>]) -> Option<(String, i128, bool)> {
            if let ChcExpr::Var(v) = args[0].as_ref() {
                if let Some(n) = args[1].as_i128() {
                    return Some((v.name.clone(), n, true));
                }
            }
            if let ChcExpr::Var(v) = args[1].as_ref() {
                if let Some(n) = args[0].as_i128() {
                    return Some((v.name.clone(), n, false));
                }
            }
            None
        }

        fn set_min(bounds: &mut FxHashMap<String, InitIntBounds>, var: String, val: i128) {
            bounds
                .entry(var)
                .and_modify(|b| b.min = b.min.max(val))
                .or_insert_with(|| {
                    let mut b = InitIntBounds::unbounded();
                    b.min = val;
                    b
                });
        }

        fn set_max(bounds: &mut FxHashMap<String, InitIntBounds>, var: String, val: i128) {
            bounds
                .entry(var)
                .and_modify(|b| b.max = b.max.min(val))
                .or_insert_with(|| {
                    let mut b = InitIntBounds::unbounded();
                    b.max = val;
                    b
                });
        }

        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::tighten_bounds_from_constraint(arg, bounds);
                }
            }
            // (>= var const) -> var >= const
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                if let Some((var, n, true)) = extract_var_const(args) {
                    set_min(bounds, var, n);
                }
            }
            // (> var const) -> var >= const + 1
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                if let Some((var, n, true)) = extract_var_const(args) {
                    set_min(bounds, var, n + 1);
                }
            }
            // (<= var const) -> var <= const
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                if let Some((var, n, true)) = extract_var_const(args) {
                    set_max(bounds, var, n);
                }
            }
            // (< var const) -> var <= const - 1
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                if let Some((var, n, true)) = extract_var_const(args) {
                    set_max(bounds, var, n - 1);
                }
            }
            // Handle negated comparisons (common in CHC constraints)
            ChcExpr::Op(ChcOp::Not, not_args) if not_args.len() == 1 => {
                match not_args[0].as_ref() {
                    // (not (<= A B)) -> A > B
                    ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                        if let Some((var, n, var_is_lhs)) = extract_var_const(args) {
                            if var_is_lhs {
                                // (not (<= var const)) -> var > const -> var >= const + 1
                                set_min(bounds, var, n + 1);
                            } else {
                                // (not (<= const var)) -> const > var -> var <= const - 1
                                set_max(bounds, var, n - 1);
                            }
                        }
                    }
                    // (not (< A B)) -> A >= B
                    ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                        if let Some((var, n, var_is_lhs)) = extract_var_const(args) {
                            if var_is_lhs {
                                // (not (< var const)) -> var >= const
                                set_min(bounds, var, n);
                            } else {
                                // (not (< const var)) -> const >= var -> var <= const
                                set_max(bounds, var, n);
                            }
                        }
                    }
                    // (not (>= A B)) -> A < B
                    ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                        if let Some((var, n, var_is_lhs)) = extract_var_const(args) {
                            if var_is_lhs {
                                // (not (>= var const)) -> var < const -> var <= const - 1
                                set_max(bounds, var, n - 1);
                            } else {
                                // (not (>= const var)) -> const < var -> var >= const + 1
                                set_min(bounds, var, n + 1);
                            }
                        }
                    }
                    // (not (> A B)) -> A <= B
                    ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                        if let Some((var, n, var_is_lhs)) = extract_var_const(args) {
                            if var_is_lhs {
                                // (not (> var const)) -> var <= const
                                set_max(bounds, var, n);
                            } else {
                                // (not (> const var)) -> const <= var -> var >= const
                                set_min(bounds, var, n);
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    /// Extract equalities from constraint
    fn extract_equalities_from_constraint(
        expr: &ChcExpr,
        head_var_to_canon: &FxHashMap<String, String>,
        body_var_bounds: &FxHashMap<String, InitIntBounds>,
        values: &mut FxHashMap<String, InitIntBounds>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::extract_equalities_from_constraint(
                        arg,
                        head_var_to_canon,
                        body_var_bounds,
                        values,
                    );
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let (left, right) = (args[0].as_ref(), args[1].as_ref());

                // Pattern: head_var = body_var or head_var = const
                if let ChcExpr::Var(hv) = left {
                    if let Some(canon_name) = head_var_to_canon.get(&hv.name) {
                        // Skip if already has bounds
                        if values.contains_key(canon_name) {
                            return;
                        }

                        // Try to compute bounds for the right-hand side
                        if let Some(computed) =
                            Self::compute_bounds_for_expr(right, body_var_bounds)
                        {
                            values.insert(canon_name.clone(), computed);
                        }
                    }
                }

                // Pattern: body_var = head_var or const = head_var
                if let ChcExpr::Var(hv) = right {
                    if let Some(canon_name) = head_var_to_canon.get(&hv.name) {
                        // Skip if already has bounds
                        if values.contains_key(canon_name) {
                            return;
                        }

                        // Try to compute bounds for the left-hand side
                        if let Some(computed) = Self::compute_bounds_for_expr(left, body_var_bounds)
                        {
                            values.insert(canon_name.clone(), computed);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// Compute bounds for an expression given bounds for variables
    pub(in crate::pdr) fn compute_bounds_for_expr(
        expr: &ChcExpr,
        var_bounds: &FxHashMap<String, InitIntBounds>,
    ) -> Option<InitIntBounds> {
        match expr {
            ChcExpr::Int(n) => Some(InitIntBounds::new(*n)),
            ChcExpr::Var(v) => var_bounds.get(&v.name).copied(),
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                let bounds0 = Self::compute_bounds_for_expr(&args[0], var_bounds)?;
                let bounds1 = Self::compute_bounds_for_expr(&args[1], var_bounds)?;
                Some(InitIntBounds {
                    min: bounds0.min.saturating_add(bounds1.min),
                    max: bounds0.max.saturating_add(bounds1.max),
                })
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                let bounds0 = Self::compute_bounds_for_expr(&args[0], var_bounds)?;
                let bounds1 = Self::compute_bounds_for_expr(&args[1], var_bounds)?;
                // min(a - b) = min_a - max_b, max(a - b) = max_a - min_b
                Some(InitIntBounds {
                    min: bounds0.min.saturating_sub(bounds1.max),
                    max: bounds0.max.saturating_sub(bounds1.min),
                })
            }
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                // Only handle constant multiplication for simplicity
                let bounds0 = Self::compute_bounds_for_expr(&args[0], var_bounds)?;
                let bounds1 = Self::compute_bounds_for_expr(&args[1], var_bounds)?;
                // Simple case: both are points (min = max)
                if bounds0.min == bounds0.max && bounds1.min == bounds1.max {
                    let result = bounds0.min.saturating_mul(bounds1.min);
                    return Some(InitIntBounds::new(result));
                }
                // General case: compute all four products and take min/max
                let products = [
                    bounds0.min.saturating_mul(bounds1.min),
                    bounds0.min.saturating_mul(bounds1.max),
                    bounds0.max.saturating_mul(bounds1.min),
                    bounds0.max.saturating_mul(bounds1.max),
                ];
                Some(InitIntBounds {
                    min: *products.iter().min().expect("fixed-size array"),
                    max: *products.iter().max().expect("fixed-size array"),
                })
            }
            _ => None, // Unsupported expression
        }
    }
}
