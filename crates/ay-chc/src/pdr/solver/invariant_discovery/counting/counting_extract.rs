// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pattern extraction helpers for counting-based invariant discovery.

use super::*;

impl PdrSolver {
    /// Extract counting error pattern: (var_a >= k * var_c) ∧ (var_b ≠ k * var_c)
    ///
    /// Returns (guard_expr, k, conclusion_var, multiplier_var) if pattern matches.
    pub(in crate::pdr::solver) fn extract_counting_error_pattern(
        constraint: &ChcExpr,
        var_map: &FxHashMap<String, (usize, String)>,
    ) -> Option<(ChcExpr, i128, String, String)> {
        // Collect conjuncts
        let conjuncts = constraint.collect_conjuncts();

        // Look for patterns:
        // 1. (>= A (* k C)) - guard condition
        // 2. (not (= B (* k C))) - negated conclusion
        let mut guard: Option<(ChcExpr, String, i128, String)> = None; // (expr, var_a, k, var_c)
        let mut negated_eq: Option<(String, i128, String)> = None; // (var_b, k, var_c)

        for conj in &conjuncts {
            // Try to match (>= var (* k other_var)) or (>= (* k var) other_var)
            if let ChcExpr::Op(ChcOp::Ge, args) = conj {
                if args.len() == 2 {
                    if let Some((var_a, k, var_c)) =
                        Self::extract_ge_mult_pattern(&args[0], &args[1], var_map)
                    {
                        guard = Some((conj.clone(), var_a, k, var_c));
                    }
                }
            }

            // Try to match (not (= var (* k other_var)))
            if let ChcExpr::Op(ChcOp::Not, args) = conj {
                if args.len() == 1 {
                    if let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() {
                        if eq_args.len() == 2 {
                            if let Some((var_b, k, var_c)) =
                                Self::extract_eq_mult_pattern(&eq_args[0], &eq_args[1], var_map)
                            {
                                negated_eq = Some((var_b, k, var_c));
                            }
                        }
                    }
                }
            }
        }

        // Match: guard has (var_a >= k * var_c) and negated_eq has (var_b != k * var_c)
        // with the same k and var_c
        if let (Some((guard_expr, _var_a, k1, var_c1)), Some((var_b, k2, var_c2))) =
            (guard, negated_eq)
        {
            if k1 == k2 && var_c1 == var_c2 {
                return Some((guard_expr, k1, var_b, var_c1));
            }
        }

        None
    }

    /// Extract simple negated equality: (guard_conjuncts) ∧ (X ≠ Y) where X,Y are vars.
    ///
    /// Returns (guard_expr, canonical_var1, canonical_var2) if pattern matches.
    /// Variables use canonical predicate names via `var_map`.
    pub(in crate::pdr::solver) fn extract_simple_negated_equality(
        constraint: &ChcExpr,
        var_map: &FxHashMap<String, (usize, String)>,
    ) -> Option<(ChcExpr, String, String)> {
        let conjuncts = constraint.collect_conjuncts();

        for (i, conj) in conjuncts.iter().enumerate() {
            let (lhs, rhs) = match conj {
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
                    ChcExpr::Op(ChcOp::Eq, eq_args) if eq_args.len() == 2 => {
                        match (eq_args[0].as_ref(), eq_args[1].as_ref()) {
                            (ChcExpr::Var(lhs), ChcExpr::Var(rhs)) => (lhs, rhs),
                            _ => continue,
                        }
                    }
                    _ => continue,
                },
                _ => continue,
            };

            // Only support int variables for now (matches how we build the conclusion vars below).
            if !matches!(lhs.sort, ChcSort::Int) || !matches!(rhs.sort, ChcSort::Int) {
                continue;
            }

            let (Some((_, c1)), Some((_, c2))) = (var_map.get(&lhs.name), var_map.get(&rhs.name))
            else {
                continue;
            };

            // Guard = AND of all other conjuncts, transformed to canonical vars.
            let guard_parts: Vec<ChcExpr> = conjuncts
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, c)| Self::transform_to_canonical_vars(c, var_map))
                .collect();
            let guard = ChcExpr::and_all(guard_parts);

            return Some((guard, c1.clone(), c2.clone()));
        }

        None
    }

    /// Extract disjunctive safety consequence from interval-conflict error clauses.
    ///
    /// Pattern: `(<= x p) ∧ (>= y p)` implies `x > p ∨ y < p`.
    /// Returned formula uses canonical variable names.
    pub(in crate::pdr::solver) fn extract_interval_conflict_disjunction(
        constraint: &ChcExpr,
        var_map: &FxHashMap<String, (usize, String)>,
    ) -> Option<ChcExpr> {
        #[derive(Clone)]
        struct VarIneq {
            is_le: bool,
            lhs: String,
            rhs: String,
            canonical_expr: ChcExpr,
        }

        let mut inequalities: Vec<VarIneq> = Vec::new();
        for conj in constraint.collect_conjuncts() {
            let (is_le, args) = match &conj {
                ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => (true, args),
                ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => (false, args),
                _ => continue,
            };
            let (lhs, rhs) = match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(lhs), ChcExpr::Var(rhs)) => (lhs, rhs),
                _ => continue,
            };
            let (Some((_, lhs_canon)), Some((_, rhs_canon))) =
                (var_map.get(&lhs.name), var_map.get(&rhs.name))
            else {
                continue;
            };
            inequalities.push(VarIneq {
                is_le,
                lhs: lhs_canon.clone(),
                rhs: rhs_canon.clone(),
                canonical_expr: Self::transform_to_canonical_vars(&conj, var_map),
            });
        }

        for i in 0..inequalities.len() {
            for j in (i + 1)..inequalities.len() {
                let first = &inequalities[i];
                let second = &inequalities[j];
                let (le, ge) = if first.is_le && !second.is_le {
                    (first, second)
                } else if second.is_le && !first.is_le {
                    (second, first)
                } else {
                    continue;
                };

                // Need a shared pivot `p` in x <= p and y >= p.
                if le.rhs != ge.rhs || le.lhs == le.rhs || ge.lhs == ge.rhs {
                    continue;
                }

                return Some(ChcExpr::or(
                    ChcExpr::not(le.canonical_expr.clone()),
                    ChcExpr::not(ge.canonical_expr.clone()),
                ));
            }
        }

        None
    }

    /// Extract pattern: var >= k * other_var
    pub(in crate::pdr::solver) fn extract_ge_mult_pattern(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        var_map: &FxHashMap<String, (usize, String)>,
    ) -> Option<(String, i128, String)> {
        // Pattern: var >= (* k other_var)
        if let ChcExpr::Var(v) = lhs {
            if let Some((_, canon_a)) = var_map.get(&v.name) {
                if let Some((k, canon_c)) = Self::extract_mult_expr(rhs, var_map) {
                    return Some((canon_a.clone(), k, canon_c));
                }
            }
        }
        None
    }

    /// Extract pattern: var = k * other_var
    pub(in crate::pdr::solver) fn extract_eq_mult_pattern(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        var_map: &FxHashMap<String, (usize, String)>,
    ) -> Option<(String, i128, String)> {
        // Try var = (* k other)
        if let ChcExpr::Var(v) = lhs {
            if let Some((_, canon_b)) = var_map.get(&v.name) {
                if let Some((k, canon_c)) = Self::extract_mult_expr(rhs, var_map) {
                    return Some((canon_b.clone(), k, canon_c));
                }
            }
        }
        // Try (* k other) = var
        if let ChcExpr::Var(v) = rhs {
            if let Some((_, canon_b)) = var_map.get(&v.name) {
                if let Some((k, canon_c)) = Self::extract_mult_expr(lhs, var_map) {
                    return Some((canon_b.clone(), k, canon_c));
                }
            }
        }
        None
    }

    /// Transform an expression to use canonical variable names.
    /// Delegates to `ChcExpr::rename_vars` (#3577).
    pub(in crate::pdr::solver) fn transform_to_canonical_vars(
        expr: &ChcExpr,
        var_map: &FxHashMap<String, (usize, String)>,
    ) -> ChcExpr {
        let name_map: FxHashMap<String, String> = var_map
            .iter()
            .map(|(k, (_, canon))| (k.clone(), canon.clone()))
            .collect();
        expr.rename_vars(&name_map)
    }

    /// Extract invariant from negated mod equality in error clause. (#1362)
    ///
    /// Pattern: `(not (= (mod Var K) R))` where Var maps to a canonical variable.
    /// Returns the positive form `(= (mod CanonVar K) R)`.
    pub(super) fn extract_negated_mod_equality(
        constraint: &ChcExpr,
        var_map: &FxHashMap<String, (usize, String)>,
    ) -> Option<ChcExpr> {
        // Match: (not (= (mod Var K) R)) or (not (= R (mod Var K)))
        let inner = match constraint {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => args[0].as_ref(),
            _ => return None,
        };
        let (lhs, rhs) = match inner {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => (args[0].as_ref(), args[1].as_ref()),
            _ => return None,
        };

        // Identify which side is (mod Var K)
        let (mod_side, val_side) = if Self::is_mod_expr(lhs) {
            (lhs, rhs)
        } else if Self::is_mod_expr(rhs) {
            (rhs, lhs)
        } else {
            return None;
        };

        // Verify the mod expression has variable argument(s) that map to canonical vars.
        // After multi-def inlining (#1362), the mod argument may be a complex expression
        // like (+ A__inline_7 B__inline_8) instead of a single variable.
        if let ChcExpr::Op(ChcOp::Mod, mod_args) = mod_side {
            if mod_args.len() == 2 {
                let mod_arg_vars = mod_args[0].vars();
                let all_mapped = !mod_arg_vars.is_empty()
                    && mod_arg_vars.iter().all(|v| var_map.contains_key(&v.name));
                if all_mapped {
                    // Substitute body arg names → canonical var names
                    let canonical = Self::transform_to_canonical_vars(
                        &ChcExpr::eq(mod_side.clone(), val_side.clone()),
                        var_map,
                    );
                    return Some(canonical);
                }
            }
        }

        None
    }

    /// Build variable substitution from equality conjuncts. (#1362)
    ///
    /// Given conjuncts like `(= X expr)` where `X` is a simple variable NOT in var_map
    /// but `expr` contains only var_map variables (or transitively resolves to such),
    /// build a map from X → expr. This allows resolving `(mod X 6)` to `(mod expr 6)`.
    ///
    /// Uses fixed-point iteration: after the first pass collects e.g.
    /// `arg0__inline_6 → (+ A__inline_7 B__inline_8)`, a second pass discovers
    /// `A → arg0__inline_6` (since arg0__inline_6 is now in subst), and transitive
    /// resolution yields `A → (+ A__inline_7 B__inline_8)`.
    pub(super) fn build_equality_subst<'a>(
        conjuncts: &[&'a ChcExpr],
        var_map: &FxHashMap<String, (usize, String)>,
    ) -> FxHashMap<String, &'a ChcExpr> {
        let mut subst: FxHashMap<String, &ChcExpr> = FxHashMap::default();

        // Fixed-point: re-scan conjuncts until no new entries are added.
        // Typical convergence in 2 passes for multi-def inlining patterns.
        for _ in 0..3 {
            let prev_len = subst.len();
            for conjunct in conjuncts {
                if let ChcExpr::Op(ChcOp::Eq, args) = conjunct {
                    if args.len() == 2 {
                        let (lhs, rhs) = (args[0].as_ref(), args[1].as_ref());
                        for (var_side, expr_side) in [(lhs, rhs), (rhs, lhs)] {
                            if let ChcExpr::Var(v) = var_side {
                                if !var_map.contains_key(&v.name) && !subst.contains_key(&v.name) {
                                    let expr_vars = expr_side.vars();
                                    let all_known = !expr_vars.is_empty()
                                        && expr_vars.iter().all(|ev| {
                                            var_map.contains_key(&ev.name)
                                                || subst.contains_key(&ev.name)
                                        });
                                    if all_known {
                                        subst.insert(v.name.clone(), expr_side);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if subst.len() == prev_len {
                break; // Fixed point reached
            }
        }

        // Resolve transitive mappings: if X → Y and Y → expr, set X → expr.
        let keys: Vec<String> = subst.keys().cloned().collect();
        for key in &keys {
            if let Some(&ChcExpr::Var(target)) = subst.get(key) {
                if let Some(&resolved) = subst.get(&target.name) {
                    let resolved_vars = resolved.vars();
                    let all_mapped = !resolved_vars.is_empty()
                        && resolved_vars.iter().all(|v| var_map.contains_key(&v.name));
                    if all_mapped {
                        subst.insert(key.clone(), resolved);
                    }
                }
            }
        }

        subst
    }

    /// Apply variable substitution to an expression. (#1362)
    pub(super) fn apply_subst(expr: &ChcExpr, subst: &FxHashMap<String, &ChcExpr>) -> ChcExpr {
        match expr {
            ChcExpr::Var(v) => {
                if let Some(&replacement) = subst.get(&v.name) {
                    replacement.clone()
                } else {
                    expr.clone()
                }
            }
            ChcExpr::Op(op, args) => {
                let new_args: Vec<std::sync::Arc<ChcExpr>> = args
                    .iter()
                    .map(|a| std::sync::Arc::new(Self::apply_subst(a.as_ref(), subst)))
                    .collect();
                ChcExpr::Op(*op, new_args)
            }
            _ => expr.clone(),
        }
    }

    /// Extract (var, k, r) from a mod equality `(= (mod var k) r)`.
    /// Returns None if the expression is not a mod equality with an integer constant RHS.
    pub(super) fn extract_mod_equality_components(expr: &ChcExpr) -> Option<(ChcVar, i128, i128)> {
        let (lhs, rhs) = match expr {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => (args[0].as_ref(), args[1].as_ref()),
            _ => return None,
        };
        // Try (mod var k) = r
        let (mod_side, val_side) = if Self::is_mod_expr(lhs) {
            (lhs, rhs)
        } else if Self::is_mod_expr(rhs) {
            (rhs, lhs)
        } else {
            return None;
        };
        let r = val_side.as_i128()?;
        if let ChcExpr::Op(ChcOp::Mod, mod_args) = mod_side {
            if mod_args.len() == 2 {
                if let ChcExpr::Var(v) = mod_args[0].as_ref() {
                    let k = mod_args[1].as_i128()?;
                    return Some((v.clone(), k, r));
                }
            }
        }
        None
    }

    pub(super) fn is_mod_expr(expr: &ChcExpr) -> bool {
        matches!(expr, ChcExpr::Op(ChcOp::Mod, _))
    }

    /// Extract k and var from (* k var) expression.
    /// Handles Op(Neg,[Int(n)]) for negative coefficients via `ChcExpr::as_i128()`.
    pub(in crate::pdr::solver) fn extract_mult_expr(
        expr: &ChcExpr,
        var_map: &FxHashMap<String, (usize, String)>,
    ) -> Option<(i128, String)> {
        if let ChcExpr::Op(ChcOp::Mul, args) = expr {
            if args.len() == 2 {
                // (* k var) or (* var k)
                if let Some(k) = args[0].as_i128() {
                    if let ChcExpr::Var(v) = args[1].as_ref() {
                        if let Some((_, canon)) = var_map.get(&v.name) {
                            return Some((k, canon.clone()));
                        }
                    }
                }
                if let Some(k) = args[1].as_i128() {
                    if let ChcExpr::Var(v) = args[0].as_ref() {
                        if let Some((_, canon)) = var_map.get(&v.name) {
                            return Some((k, canon.clone()));
                        }
                    }
                }
            }
        }
        None
    }
}
