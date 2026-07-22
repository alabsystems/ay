// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Invariant translation across clause mappings.
//!
//! Translates a discovered invariant from one predicate's canonical variables
//! to another predicate's canonical variables using the clause structure
//! (body args, head args, constraint equalities).

use super::super::super::PdrSolver;

use crate::{ChcExpr, ChcOp, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl PdrSolver {
    pub(super) fn translate_invariant_via_clause_mapping(
        &self,
        source_pred: PredicateId,
        target_pred: PredicateId,
        source_formula: &ChcExpr,
        body_args: &[ChcExpr],
        head_args: &[ChcExpr],
        constraint: Option<&ChcExpr>,
    ) -> Option<ChcExpr> {
        let source_vars = self.canonical_vars(source_pred)?;
        let target_vars = self.canonical_vars(target_pred)?;

        if source_vars.len() != body_args.len() {
            return None;
        }
        if target_vars.len() != head_args.len() {
            return None;
        }

        // Compute which source canonical vars are actually used by the formula.
        let mut source_name_to_idx: FxHashMap<&str, usize> = FxHashMap::default();
        for (idx, v) in source_vars.iter().enumerate() {
            source_name_to_idx.insert(v.name.as_str(), idx);
        }

        let mut used_source_indices: Vec<usize> = Vec::new();
        for v in source_formula.vars() {
            let Some(idx) = source_name_to_idx.get(v.name.as_str()).copied() else {
                // The formula is not purely over source canonical vars (unexpected); skip.
                return None;
            };
            if !used_source_indices.contains(&idx) {
                used_source_indices.push(idx);
            }
        }
        if used_source_indices.is_empty() {
            return None;
        }

        let target_names: FxHashSet<String> = target_vars.iter().map(|v| v.name.clone()).collect();
        let clause_to_target =
            build_clause_local_to_target_substitutions(target_vars, head_args, constraint);

        let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for i in used_source_indices {
            let rewritten = body_args[i]
                .substitute_name_map(&clause_to_target)
                .simplify_constants();
            if !expr_vars_are_target_grounded(&rewritten, &target_names) {
                return None;
            }
            subst.push((source_vars[i].clone(), rewritten));
        }

        let translated = source_formula.substitute(&subst).simplify_constants();
        if expr_vars_are_target_grounded(&translated, &target_names) {
            Some(translated)
        } else {
            None
        }
    }
}

pub(super) fn derive_target_var_permutation(
    target_vars: &[ChcVar],
    body_args: &[ChcExpr],
    head_args: &[ChcExpr],
    constraint: Option<&ChcExpr>,
) -> Option<Vec<usize>> {
    if target_vars.len() != head_args.len() || body_args.len() != target_vars.len() {
        return None;
    }

    let clause_to_target =
        build_clause_local_to_target_substitutions(target_vars, head_args, constraint);
    let target_name_to_idx: FxHashMap<&str, usize> = target_vars
        .iter()
        .enumerate()
        .map(|(idx, var)| (var.name.as_str(), idx))
        .collect();

    let mut permutation = Vec::with_capacity(body_args.len());
    let mut seen_targets = vec![false; target_vars.len()];

    for body_arg in body_args {
        let rewritten = body_arg
            .substitute_name_map(&clause_to_target)
            .simplify_constants();
        let ChcExpr::Var(ref var) = rewritten else {
            return None;
        };
        let &target_idx = target_name_to_idx.get(var.name.as_str())?;
        if seen_targets[target_idx] {
            return None;
        }
        seen_targets[target_idx] = true;
        permutation.push(target_idx);
    }

    if seen_targets.into_iter().all(|seen| seen) {
        Some(permutation)
    } else {
        None
    }
}

fn build_clause_local_to_target_substitutions(
    target_vars: &[ChcVar],
    head_args: &[ChcExpr],
    constraint: Option<&ChcExpr>,
) -> FxHashMap<String, ChcExpr> {
    let target_names: FxHashSet<String> = target_vars.iter().map(|v| v.name.clone()).collect();
    let mut equations = Vec::new();

    for (target_var, head_arg) in target_vars.iter().zip(head_args) {
        equations.push((ChcExpr::var(target_var.clone()), head_arg.clone()));
    }
    if let Some(c) = constraint {
        collect_equality_conjuncts(c, &mut equations);
    }

    let mut subst = FxHashMap::default();
    let max_rounds = equations.len().saturating_mul(2).max(1);
    for _ in 0..max_rounds {
        let mut progress = false;
        for (lhs_raw, rhs_raw) in &equations {
            let lhs = lhs_raw.substitute_name_map(&subst).simplify_constants();
            let rhs = rhs_raw.substitute_name_map(&subst).simplify_constants();
            let Some((name, expr)) = solve_equality_for_clause_local_var(&lhs, &rhs, &target_names)
            else {
                continue;
            };
            if subst.contains_key(&name) {
                continue;
            }

            let expr = expr.substitute_name_map(&subst).simplify_constants();
            if !expr_vars_are_target_grounded(&expr, &target_names) {
                continue;
            }
            if expr.vars().into_iter().any(|v| v.name == name) {
                continue;
            }

            subst.insert(name, expr);
            progress = true;
        }
        if !progress {
            break;
        }
    }

    subst
}

fn collect_equality_conjuncts(expr: &ChcExpr, equations: &mut Vec<(ChcExpr, ChcExpr)>) {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => {
            for arg in args {
                collect_equality_conjuncts(arg, equations);
            }
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            equations.push(((*args[0]).clone(), (*args[1]).clone()));
        }
        _ => {}
    }
}

fn expr_vars_are_target_grounded(expr: &ChcExpr, target_names: &FxHashSet<String>) -> bool {
    expr.vars()
        .into_iter()
        .all(|var| target_names.contains(&var.name))
}

fn solve_equality_for_clause_local_var(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    target_names: &FxHashSet<String>,
) -> Option<(String, ChcExpr)> {
    if let ChcExpr::Var(v) = lhs {
        if !target_names.contains(&v.name) && !rhs.vars().iter().any(|rhs_v| rhs_v.name == v.name) {
            return Some((v.name.clone(), rhs.clone()));
        }
    }
    if let ChcExpr::Var(v) = rhs {
        if !target_names.contains(&v.name) && !lhs.vars().iter().any(|lhs_v| lhs_v.name == v.name) {
            return Some((v.name.clone(), lhs.clone()));
        }
    }

    let diff = ChcExpr::sub(lhs.clone(), rhs.clone());
    let mut terms = Vec::new();
    let mut eq_constant = 0i128;
    if !collect_linear_terms(&diff, 1, &mut terms, &mut eq_constant) {
        return None;
    }

    for i in 0..terms.len() {
        let (coeff, ref name) = terms[i];
        if (coeff != 1 && coeff != -1) || target_names.contains(name) {
            continue;
        }

        // Solve: coeff*name + other_terms + eq_constant = 0
        // -> name = -(other_terms + eq_constant) / coeff
        let mut other_sum = Vec::new();
        for (j, (c, n)) in terms.iter().enumerate() {
            if j == i {
                continue;
            }
            let adjusted_c = c.checked_neg()?.checked_mul(coeff)?;
            if adjusted_c == 1 {
                other_sum.push(ChcExpr::var(ChcVar::new(n.clone(), crate::ChcSort::Int)));
            } else if adjusted_c == -1 {
                other_sum.push(ChcExpr::neg(ChcExpr::var(ChcVar::new(
                    n.clone(),
                    crate::ChcSort::Int,
                ))));
            } else {
                other_sum.push(ChcExpr::mul(
                    ChcExpr::int(adjusted_c),
                    ChcExpr::var(ChcVar::new(n.clone(), crate::ChcSort::Int)),
                ));
            }
        }
        let adjusted_constant = eq_constant.checked_neg()?.checked_mul(coeff)?;
        if adjusted_constant != 0 {
            other_sum.push(ChcExpr::int(adjusted_constant));
        }

        let rhs_expr = if other_sum.is_empty() {
            ChcExpr::int(0)
        } else {
            other_sum
                .into_iter()
                .reduce(ChcExpr::add)
                .unwrap_or_else(|| ChcExpr::int(0))
        }
        .simplify_constants();

        if !rhs_expr.vars().iter().any(|v| v.name == *name) {
            return Some((name.clone(), rhs_expr));
        }
    }

    None
}

/// Collect linear terms from a CHC expression.
///
/// Returns `true` if the expression is linear, accumulating into `terms` and `constant`.
fn collect_linear_terms(
    expr: &ChcExpr,
    sign: i128,
    terms: &mut Vec<(i128, String)>,
    constant: &mut i128,
) -> bool {
    match expr {
        ChcExpr::Int(k) => sign
            .checked_mul(*k)
            .and_then(|scaled| constant.checked_add(scaled))
            .is_some_and(|next| {
                *constant = next;
                true
            }),
        ChcExpr::Var(v) => {
            terms.push((sign, v.name.clone()));
            true
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => sign
            .checked_neg()
            .is_some_and(|neg_sign| collect_linear_terms(&args[0], neg_sign, terms, constant)),
        ChcExpr::Op(ChcOp::Add, args) => args
            .iter()
            .all(|arg| collect_linear_terms(arg, sign, terms, constant)),
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            sign.checked_neg().is_some_and(|neg_sign| {
                collect_linear_terms(&args[0], sign, terms, constant)
                    && collect_linear_terms(&args[1], neg_sign, terms, constant)
            })
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            if let ChcExpr::Int(k) = &*args[0] {
                sign.checked_mul(*k)
                    .is_some_and(|scaled| collect_linear_terms(&args[1], scaled, terms, constant))
            } else if let ChcExpr::Int(k) = &*args[1] {
                sign.checked_mul(*k)
                    .is_some_and(|scaled| collect_linear_terms(&args[0], scaled, terms, constant))
            } else {
                false
            }
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ChcSort;

    #[test]
    fn collect_linear_terms_rejects_coefficient_overflow() {
        // i128-lockstep: the rejection boundary moved to i128.
        let expr = ChcExpr::mul(
            ChcExpr::int(i128::MAX),
            ChcExpr::mul(
                ChcExpr::int(2),
                ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ),
        );
        let mut terms = Vec::new();
        let mut constant = 0;

        assert!(!collect_linear_terms(&expr, 1, &mut terms, &mut constant));
    }

    #[test]
    fn collect_linear_terms_rejects_constant_overflow() {
        // i128-lockstep: the rejection boundary moved to i128.
        let expr = ChcExpr::add(ChcExpr::int(i128::MAX), ChcExpr::int(1));
        let mut terms = Vec::new();
        let mut constant = 0;

        assert!(!collect_linear_terms(&expr, 1, &mut terms, &mut constant));
    }
}
