// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Utility methods for transition equality analysis: boundary extraction,
//! canonical variable mapping, multiplicative bound extraction, and
//! propagation entry constraints.

use super::*;

impl PdrSolver {
    pub(in crate::pdr::solver) fn constraint_contains_equality(
        constraint: &ChcExpr,
        lhs: &ChcExpr,
        rhs: &ChcExpr,
    ) -> bool {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => args
                .iter()
                .any(|arg| Self::constraint_contains_equality(arg, lhs, rhs)),
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                (args[0].as_ref() == lhs && args[1].as_ref() == rhs)
                    || (args[0].as_ref() == rhs && args[1].as_ref() == lhs)
            }
            _ => false,
        }
    }

    /// Convert boundary equalities from a transition constraint to canonical variable form.
    ///
    /// This maps the raw variable names in the constraint to canonical variables,
    /// so that the entry constraint can be used in the self-loop preservation check.
    pub(in crate::pdr::solver) fn boundary_to_canonical_entry_constraint(
        constraint: &ChcExpr,
        head_args: &[ChcExpr],
        head_vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        // Build a map from variable names in head_args to canonical variable names.
        // #2492: For expression head args, map all constituent vars to the
        // canonical var (first-seen wins via entry to avoid clobber).
        let mut var_to_canonical: FxHashMap<String, ChcVar> = FxHashMap::default();
        for (arg, canon) in head_args.iter().zip(head_vars.iter()) {
            match arg {
                ChcExpr::Var(v) => {
                    var_to_canonical.insert(v.name.clone(), canon.clone());
                }
                expr => {
                    for v in expr.vars() {
                        var_to_canonical
                            .entry(v.name.clone())
                            .or_insert_with(|| canon.clone());
                    }
                }
            }
        }

        // Extract boundary equalities and convert to canonical form
        let boundary_eqs = Self::extract_boundary_equalities(constraint);
        if boundary_eqs.is_empty() {
            return None;
        }

        let canonical_eqs: Vec<ChcExpr> = boundary_eqs
            .into_iter()
            .filter_map(|eq| Self::to_canonical(&eq, &var_to_canonical))
            .collect();

        if canonical_eqs.is_empty() {
            None
        } else {
            Some(
                canonical_eqs
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .unwrap_or(ChcExpr::Bool(true)),
            )
        }
    }

    /// Convert an expression to use canonical variable names.
    pub(in crate::pdr::solver) fn to_canonical(
        expr: &ChcExpr,
        var_map: &FxHashMap<String, ChcVar>,
    ) -> Option<ChcExpr> {
        match expr {
            ChcExpr::Bool(b) => Some(ChcExpr::Bool(*b)),
            ChcExpr::Int(n) => Some(ChcExpr::Int(*n)),
            ChcExpr::BitVec(val, width) => Some(ChcExpr::BitVec(*val, *width)),
            ChcExpr::Real(n, d) => Some(ChcExpr::Real(*n, *d)),
            ChcExpr::Var(v) => {
                if let Some(canon) = var_map.get(&v.name) {
                    Some(ChcExpr::var(canon.clone()))
                } else {
                    // Variable not in map - keep original (might be a local variable)
                    Some(ChcExpr::var(v.clone()))
                }
            }
            ChcExpr::Op(op, args) => {
                let conv_args: Option<Vec<_>> = args
                    .iter()
                    .map(|a| Self::to_canonical(a, var_map).map(std::sync::Arc::new))
                    .collect();
                conv_args.map(|a| ChcExpr::Op(*op, a))
            }
            ChcExpr::PredicateApp(name, id, args) => {
                let conv_args: Option<Vec<_>> = args
                    .iter()
                    .map(|a| Self::to_canonical(a, var_map))
                    .collect();
                conv_args.map(|a| ChcExpr::predicate_app(name.clone(), *id, a))
            }
            ChcExpr::FuncApp(name, sort, args) => {
                let conv_args: Option<Vec<_>> = args
                    .iter()
                    .map(|a| Self::to_canonical(a, var_map).map(std::sync::Arc::new))
                    .collect();
                conv_args.map(|a| ChcExpr::FuncApp(name.clone(), sort.clone(), a))
            }
            ChcExpr::ConstArrayMarker(ks) => Some(ChcExpr::ConstArrayMarker(ks.clone())),
            ChcExpr::IsTesterMarker(name) => Some(ChcExpr::IsTesterMarker(name.clone())),
            ChcExpr::ConstArray(ks, val) => Self::to_canonical(val, var_map)
                .map(|v| ChcExpr::ConstArray(ks.clone(), std::sync::Arc::new(v))),
        }
    }

    /// Extract boundary equalities from a constraint.
    ///
    /// For constraints like `A >= E`, returns `[A = E]` as the boundary condition.
    /// For constraints like `A > E`, returns `[A = E + 1]` (which simplifies to `A = E + 1`).
    /// This is a heuristic that assumes transitions fire at the exact boundary when
    /// the source loop increments by 1 and exits when the guard becomes false.
    pub(in crate::pdr::solver) fn extract_boundary_equalities(
        constraint: &ChcExpr,
    ) -> Vec<ChcExpr> {
        let mut equalities = Vec::new();

        match constraint {
            // Simple >= comparison: A >= E  =>  boundary is A = E
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                equalities.push(ChcExpr::eq(
                    args[0].as_ref().clone(),
                    args[1].as_ref().clone(),
                ));
            }
            // Simple > comparison: A > E  =>  boundary is A = E + 1
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                let rhs_plus_one = ChcExpr::add(args[1].as_ref().clone(), ChcExpr::Int(1));
                equalities.push(ChcExpr::eq(args[0].as_ref().clone(), rhs_plus_one));
            }
            // Simple <= comparison: A <= E  =>  boundary is A = E
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                equalities.push(ChcExpr::eq(
                    args[0].as_ref().clone(),
                    args[1].as_ref().clone(),
                ));
            }
            // Simple < comparison: A < E  =>  boundary is A = E - 1
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                let rhs_minus_one = ChcExpr::sub(args[1].as_ref().clone(), ChcExpr::Int(1));
                equalities.push(ChcExpr::eq(args[0].as_ref().clone(), rhs_minus_one));
            }
            // AND: extract from all conjuncts
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    equalities.extend(Self::extract_boundary_equalities(arg));
                }
            }
            _ => {}
        }

        equalities
    }

    /// Extract multiplicative entry bounds from a gate constraint.
    ///
    /// For constraints like `(>= A (* k D))` where A is a fresh variable and D is an argument,
    /// this extracts the bound that can be used as an entry constraint.
    ///
    /// Returns (coefficient, arg_index) if found.
    /// The bound is: fresh_var >= coefficient * arg[arg_index]
    pub(in crate::pdr::solver) fn extract_multiplicative_bound(
        constraint: &ChcExpr,
        head_args: &[ChcExpr],
    ) -> Option<(i128, usize)> {
        // Pattern: (>= A (* k D)) where A is fresh, D is an argument
        if let ChcExpr::Op(ChcOp::Ge, args) = constraint {
            if args.len() == 2 {
                // Check if RHS is (* k var) where var is an argument
                if let ChcExpr::Op(ChcOp::Mul, mul_args) = args[1].as_ref() {
                    if mul_args.len() == 2 {
                        // Try both orderings: (k, var) or (var, k)
                        let (coef, var) = if let ChcExpr::Int(k) = mul_args[0].as_ref() {
                            if let ChcExpr::Var(v) = mul_args[1].as_ref() {
                                (*k, v)
                            } else {
                                return None;
                            }
                        } else if let ChcExpr::Int(k) = mul_args[1].as_ref() {
                            if let ChcExpr::Var(v) = mul_args[0].as_ref() {
                                (*k, v)
                            } else {
                                return None;
                            }
                        } else {
                            return None;
                        };

                        // Find which argument position the variable corresponds to
                        for (idx, arg) in head_args.iter().enumerate() {
                            if let ChcExpr::Var(a) = arg {
                                if a.name == var.name {
                                    return Some((coef, idx));
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// Build an entry constraint for equality propagation through a gate clause.
    ///
    /// For a gate with constraint like `A >= k * bound_var`, where the gate passes
    /// arguments unchanged, this builds an entry constraint:
    /// - `head_vars[0] >= k * head_vars[bound_idx]` (assuming 1st arg is loop counter)
    /// - Plus the equality being propagated (e.g., `head_vars[i] = head_vars[j]`)
    pub(in crate::pdr::solver) fn build_propagation_entry_constraint(
        constraint: &Option<ChcExpr>,
        head_args: &[ChcExpr],
        head_vars: &[ChcVar],
        equality_i: usize,
        equality_j: usize,
    ) -> Option<ChcExpr> {
        let mut conjuncts: Vec<ChcExpr> = Vec::new();

        // Add the propagated equality itself as an entry constraint
        // This is key: we know the equality holds at entry (from the source predicate)
        if equality_i < head_vars.len() && equality_j < head_vars.len() {
            let eq = ChcExpr::eq(
                ChcExpr::var(head_vars[equality_i].clone()),
                ChcExpr::var(head_vars[equality_j].clone()),
            );
            conjuncts.push(eq);
        }

        // Try to extract multiplicative bound from gate constraint
        if let Some(c) = constraint {
            if let Some((coef, bound_idx)) = Self::extract_multiplicative_bound(c, head_args) {
                // Gate has bound like `fresh >= k * arg[bound_idx]`
                // Assume fresh = loop counter = 1st argument (index 0)
                // Entry constraint: head_vars[0] >= k * head_vars[bound_idx]
                if bound_idx < head_vars.len() {
                    let entry_bound = ChcExpr::ge(
                        ChcExpr::var(head_vars[0].clone()),
                        ChcExpr::mul(
                            ChcExpr::Int(coef),
                            ChcExpr::var(head_vars[bound_idx].clone()),
                        ),
                    );
                    conjuncts.push(entry_bound);
                }
            }
        }

        if conjuncts.is_empty() {
            None
        } else if conjuncts.len() == 1 {
            Some(conjuncts.pop().expect("len == 1"))
        } else {
            Some(conjuncts.into_iter().reduce(ChcExpr::and).expect("len > 1"))
        }
    }
}
