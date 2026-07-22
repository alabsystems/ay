// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression analysis: variables, equalities, linear terms, and node counting.

use std::sync::Arc;

use ay_core::kani_compat::DetHashSet as FxHashSet;

use super::{
    maybe_grow_expr_stack, walk_linear_expr, ChcExpr, ChcOp, ChcSort, ChcVar, LinearTermsProd,
    MAX_EXPR_RECURSION_DEPTH,
};

impl ChcExpr {
    /// Get all variables in the expression.
    ///
    /// Uses `FxHashSet` for O(1) deduplication, avoiding the O(n²) complexity
    /// of the previous `Vec::contains()` approach (#1120).
    pub fn vars(&self) -> Vec<ChcVar> {
        let mut seen = FxHashSet::default();
        let mut result = Vec::new();
        self.collect_vars_dedupe(&mut seen, &mut result, 0);
        result
    }

    /// Get all variables in the expression whose sort matches `sort`.
    ///
    /// Expression-valued predicate head args can contain mixed-sort
    /// constituents, such as `(select arr idx)`. Callers that canonicalize by
    /// head position must ignore non-matching sorts to avoid cross-sort
    /// rewrites (#7897).
    pub fn vars_of_sort(&self, sort: &ChcSort) -> Vec<ChcVar> {
        self.vars()
            .into_iter()
            .filter(|v| &v.sort == sort)
            .collect()
    }

    fn collect_vars_dedupe(
        &self,
        seen: &mut FxHashSet<ChcVar>,
        result: &mut Vec<ChcVar>,
        depth: usize,
    ) {
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            return;
        }
        maybe_grow_expr_stack(|| match self {
            Self::Bool(_) | Self::Int(_) | Self::Real(_, _) | Self::BitVec(_, _) => {}
            Self::Var(v) => {
                if seen.insert(v.clone()) {
                    result.push(v.clone());
                }
            }
            Self::Op(_, args) => {
                for arg in args {
                    arg.collect_vars_dedupe(seen, result, depth + 1);
                }
            }
            Self::PredicateApp(_, _, args) => {
                for arg in args {
                    arg.collect_vars_dedupe(seen, result, depth + 1);
                }
            }
            Self::FuncApp(_, _, args) => {
                for arg in args {
                    arg.collect_vars_dedupe(seen, result, depth + 1);
                }
            }
            Self::ConstArrayMarker(_) | Self::IsTesterMarker(_) => {}
            Self::ConstArray(_ks, val) => val.collect_vars_dedupe(seen, result, depth + 1),
        })
    }

    /// Check if this expression is Bool-sorted at the top level.
    ///
    /// Returns true for comparisons (Eq, Ne, Lt, Le, Gt, Ge, BvULt, etc.),
    /// Boolean connectives (And, Or, Not, Implies, Iff), Bool literals,
    /// and Bool-sorted variables. Used by #6047 to allow array-referencing
    /// invariant conjuncts that are scalar-valued (e.g., `(= (select arr idx) val)`).
    pub fn is_bool_sorted_top_level(&self) -> bool {
        match self {
            Self::Bool(_) => true,
            Self::Int(_) | Self::Real(_, _) | Self::BitVec(_, _) => false,
            Self::Var(v) => matches!(v.sort, ChcSort::Bool),
            Self::Op(op, _) => matches!(
                op,
                ChcOp::Not
                    | ChcOp::And
                    | ChcOp::Or
                    | ChcOp::Implies
                    | ChcOp::Iff
                    | ChcOp::Eq
                    | ChcOp::Ne
                    | ChcOp::Lt
                    | ChcOp::Le
                    | ChcOp::Gt
                    | ChcOp::Ge
                    | ChcOp::BvULt
                    | ChcOp::BvULe
                    | ChcOp::BvUGt
                    | ChcOp::BvUGe
                    | ChcOp::BvSLt
                    | ChcOp::BvSLe
                    | ChcOp::BvSGt
                    | ChcOp::BvSGe
            ),
            Self::PredicateApp(_, _, _) => true, // Predicates are Bool-sorted
            Self::FuncApp(_, sort, _) => matches!(sort, ChcSort::Bool),
            Self::ConstArrayMarker(_) | Self::IsTesterMarker(_) => false,
            Self::ConstArray(_, _) => false,
        }
    }

    /// Propagate constants from equalities of the form `var = constant`.
    /// This enables constant folding for expressions like `(mod A 2)` when `A = 0`.
    pub(crate) fn propagate_constants(&self) -> Self {
        // First propagate var = var equalities
        let var_propagated = self.propagate_var_equalities();

        // Extract var = const equalities from conjunction
        let equalities = var_propagated.extract_var_const_equalities();
        if equalities.is_empty() {
            // Always simplify even if no substitutions - this enables algebraic simplification
            // like (+ (+ x 1) (- y 1)) -> (+ x y)
            return var_propagated.simplify_constants();
        }

        // Build substitution list
        let subst: Vec<(ChcVar, Self)> = equalities
            .iter()
            .map(|(var, val)| (var.clone(), Self::Int(*val)))
            .collect();

        // Apply substitution and simplify
        var_propagated.substitute(&subst).simplify_constants()
    }

    /// Propagate variable equalities: if x = y, substitute all occurrences of y with x
    fn propagate_var_equalities(&self) -> Self {
        let var_eqs = self.extract_var_var_equalities();
        if var_eqs.is_empty() {
            return self.clone();
        }

        // Build substitution list: substitute second var with first
        let subst: Vec<(ChcVar, Self)> = var_eqs
            .iter()
            .map(|(v1, v2)| (v2.clone(), Self::var(v1.clone())))
            .collect();

        // Apply substitution and simplify
        self.substitute(&subst).simplify_constants()
    }

    /// (#3121) Simplify tautological equalities in a conjunction by collecting
    /// linear terms for both sides of `(= A B)`.  If `A - B` reduces to `0`
    /// (all variable coefficients cancel and the constant is 0), the equality
    /// is replaced with `true`.  This is critical for ITE-split transition
    /// constraints where self-referential equalities like
    /// `(= a2 (+ (- (- (+ 0 a1) a2)) a1))` (≡ a2 = a2) remain after
    /// constant propagation because simplify_constants cannot cancel
    /// variable terms across Add/Sub/Neg.
    pub(crate) fn simplify_linear_equalities(&self) -> Self {
        match self {
            Self::Op(ChcOp::And, args) => {
                let simplified: Vec<Arc<Self>> = args
                    .iter()
                    .filter_map(|arg| {
                        let s = arg.simplify_linear_equalities();
                        if matches!(s, Self::Bool(true)) {
                            None // drop tautological conjuncts
                        } else {
                            Some(Arc::new(s))
                        }
                    })
                    .collect();
                if simplified.is_empty() {
                    Self::Bool(true)
                } else if simplified.len() == 1 {
                    simplified
                        .into_iter()
                        .next()
                        .expect("len==1")
                        .as_ref()
                        .clone()
                } else {
                    Self::Op(ChcOp::And, simplified)
                }
            }
            Self::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Try to decompose both sides as linear combinations
                if let (Some(lhs), Some(rhs)) = (
                    Self::collect_linear_terms_prod(&args[0]),
                    Self::collect_linear_terms_prod(&args[1]),
                ) {
                    // Check if LHS - RHS = 0 (tautology)
                    let diff_const = lhs.constant - rhs.constant;
                    let mut all_zero = diff_const == 0;
                    if all_zero {
                        // Collect all variable names from both sides
                        let all_vars: FxHashSet<&str> = lhs
                            .coeffs
                            .keys()
                            .chain(rhs.coeffs.keys())
                            .map(String::as_str)
                            .collect();
                        for var in &all_vars {
                            let lc = lhs.coeffs.get(*var).copied().unwrap_or(0);
                            let rc = rhs.coeffs.get(*var).copied().unwrap_or(0);
                            if lc != rc {
                                all_zero = false;
                                break;
                            }
                        }
                    }
                    if all_zero {
                        return Self::Bool(true);
                    }
                }
                self.clone()
            }
            _ => self.clone(),
        }
    }

    /// Collect linear terms from an integer expression: result is
    /// `constant + sum(coeffs[var] * var)`.  Returns None for non-linear
    /// or non-integer expressions.
    pub(crate) fn collect_linear_terms_prod(expr: &Self) -> Option<LinearTermsProd> {
        let mut result = LinearTermsProd::default();
        walk_linear_expr(
            expr,
            1i128,
            &mut |mult, n| {
                result.constant = result.constant.checked_add(mult.checked_mul(n)?)?;
                Some(())
            },
            &mut |mult, v| {
                if !matches!(v.sort, ChcSort::Int) {
                    return None;
                }
                let entry = result.coeffs.entry(v.name.clone()).or_insert(0);
                *entry = (*entry).checked_add(mult)?;
                Some(())
            },
        )?;
        Some(result)
    }

    /// Extract (var1, var2) pairs from var = var equalities in a conjunction
    pub(crate) fn extract_var_var_equalities(&self) -> Vec<(ChcVar, ChcVar)> {
        let mut result = Vec::new();
        self.collect_var_var_equalities(&mut result, 0);
        result
    }

    fn collect_var_var_equalities(&self, result: &mut Vec<(ChcVar, ChcVar)>, depth: usize) {
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            return;
        }
        maybe_grow_expr_stack(|| match self {
            Self::Op(ChcOp::And, args) => {
                for arg in args {
                    arg.collect_var_var_equalities(result, depth + 1);
                }
            }
            Self::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check for var = var pattern
                if let (Self::Var(v1), Self::Var(v2)) = (args[0].as_ref(), args[1].as_ref()) {
                    if v1.name != v2.name {
                        result.push((v1.clone(), v2.clone()));
                    }
                }
            }
            _ => {}
        })
    }

    /// Extract (variable, constant) pairs from var = const equalities in a conjunction.
    pub(crate) fn extract_var_const_equalities(&self) -> Vec<(ChcVar, i128)> {
        let mut result = Vec::new();
        self.collect_var_const_equalities(&mut result, 0);
        result
    }

    fn collect_var_const_equalities(&self, result: &mut Vec<(ChcVar, i128)>, depth: usize) {
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            return;
        }
        maybe_grow_expr_stack(|| match self {
            Self::Op(ChcOp::And, args) => {
                for arg in args {
                    arg.collect_var_const_equalities(result, depth + 1);
                }
            }
            Self::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check for var = const pattern
                if let (Self::Var(v), Self::Int(n)) = (args[0].as_ref(), args[1].as_ref()) {
                    result.push((v.clone(), *n));
                } else if let (Self::Int(n), Self::Var(v)) = (args[0].as_ref(), args[1].as_ref()) {
                    result.push((v.clone(), *n));
                }
                // Also handle linear patterns like (= (+ k var) c) => var = c - k
                else if let Some((var, val)) =
                    Self::extract_linear_equality(args[0].as_ref(), args[1].as_ref())
                {
                    result.push((var, val));
                } else if let Some((var, val)) =
                    Self::extract_linear_equality(args[1].as_ref(), args[0].as_ref())
                {
                    result.push((var, val));
                }
            }
            _ => {}
        })
    }

    /// Extract var = value from (+ k var) = c => var = c - k
    fn extract_linear_equality(lhs: &Self, rhs: &Self) -> Option<(ChcVar, i128)> {
        let c = match rhs {
            Self::Int(n) => *n,
            _ => return None,
        };
        match lhs {
            // (+ k var) = c => var = c - k
            Self::Op(ChcOp::Add, inner) if inner.len() == 2 => {
                match (inner[0].as_ref(), inner[1].as_ref()) {
                    (Self::Int(k), Self::Var(v)) | (Self::Var(v), Self::Int(k)) => {
                        // i128-lockstep: checked (was unchecked wrap-capable);
                        // overflow → no extraction (fail-closed).
                        Some((v.clone(), c.checked_sub(*k)?))
                    }
                    _ => None,
                }
            }
            // (* -1 var) = c => var = -c
            Self::Op(ChcOp::Mul, inner) if inner.len() == 2 => {
                match (inner[0].as_ref(), inner[1].as_ref()) {
                    (Self::Int(-1), Self::Var(v)) | (Self::Var(v), Self::Int(-1)) => {
                        // i128-lockstep: checked negation (fail-closed).
                        Some((v.clone(), c.checked_neg()?))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Count expression nodes, stopping at `limit` (#2774).
    /// Returns `limit` if the expression has at least that many nodes,
    /// which lets callers test `expr.node_count(N) >= N` cheaply without
    /// traversing entire pathological trees.
    pub fn node_count(&self, limit: usize) -> usize {
        use std::cell::Cell;
        let count = Cell::new(0usize);
        fn count_inner(expr: &ChcExpr, count: &Cell<usize>, limit: usize, depth: usize) {
            if count.get() >= limit {
                return;
            }
            if depth >= MAX_EXPR_RECURSION_DEPTH {
                return;
            }
            count.set(count.get() + 1);
            maybe_grow_expr_stack(|| match expr {
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => {}
                ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
                    for a in args {
                        count_inner(a, count, limit, depth + 1);
                    }
                }
                ChcExpr::FuncApp(_, _, args) => {
                    for a in args {
                        count_inner(a, count, limit, depth + 1);
                    }
                }
                ChcExpr::ConstArray(_ks, val) => count_inner(val, count, limit, depth + 1),
            });
        }
        count_inner(self, &count, limit, 0);
        count.get()
    }
}
