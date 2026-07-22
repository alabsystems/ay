// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic pattern matcher for CHC expressions.
//!
//! This is used by lemma clustering to match semantically equivalent expressions
//! while extracting substitutions for *pattern variables* (the vars provided in
//! `pattern_vars`).
//!
//! Z3 reference: `reference/z3/src/muz/spacer/spacer_sem_matcher.cpp`.

use crate::{ChcExpr, ChcOp, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

/// Semantic matcher for `ChcExpr` patterns that contain pattern variables.
///
/// The matcher supports:
/// - Structural matching with extraction of Int bindings for `pattern_vars`.
/// - Negation equivalences for (in)equalities: `x <= y` vs `!(x > y)`, `x >= y` vs `!(x < y)`.
/// - A limited linear solve: `k + c1` matched against numeral `c2` binds `k = c2 - c1`.
/// - Signed matching at the top level by stripping a single `not` (tracking `positive`).
#[derive(Debug, Clone)]
pub(super) struct SemanticMatcher {
    positive: bool,
}

impl Default for SemanticMatcher {
    fn default() -> Self {
        Self::new()
    }
}

impl SemanticMatcher {
    pub(super) fn new() -> Self {
        Self { positive: true }
    }

    /// Match `instance` against `pattern`, extracting a substitution for `pattern_vars`.
    ///
    /// Returns `Some((positive, subst_values))` on match:
    /// - `positive=true`: `instance` matches `pattern`
    /// - `positive=false`: `not(instance)` matches `pattern` (top-level signed match)
    pub(super) fn matches_signed(
        &mut self,
        pattern: &ChcExpr,
        pattern_vars: &[ChcVar],
        instance: &ChcExpr,
    ) -> Option<(bool, Vec<i128>)> {
        self.positive = true;

        let mut var_to_idx: FxHashMap<&str, usize> = FxHashMap::default();
        for (i, v) in pattern_vars.iter().enumerate() {
            if var_to_idx.insert(v.name.as_str(), i).is_some() {
                // Duplicate pattern var name => ambiguous.
                return None;
            }
        }

        let mut subst: Vec<Option<i128>> = vec![None; pattern_vars.len()];

        let mut todo: Vec<(&ChcExpr, &ChcExpr, bool)> = vec![(pattern, instance, true)];
        while let Some((pattern, instance, top)) = todo.pop() {
            // Pattern variables bind to integer or BV numerals.
            if let ChcExpr::Var(var) = pattern {
                if let Some(&idx) = var_to_idx.get(var.name.as_str()) {
                    let value = match instance {
                        ChcExpr::Int(n) => *n,
                        ChcExpr::BitVec(v, _) => match i128::try_from(*v) {
                            Ok(n) => n,
                            Err(_) => return None,
                        },
                        _ => return None,
                    };
                    match subst[idx] {
                        Some(existing) if existing != value => return None,
                        Some(_) => {}
                        None => subst[idx] = Some(value),
                    }
                    continue;
                }
            }

            // Linear solve: k + c1 matched to c2  => k = c2 - c1.
            if let Some(ok) = self.try_linear_solve(pattern, instance, &var_to_idx, &mut subst) {
                if ok {
                    continue;
                }
                return None;
            }

            match (pattern, instance) {
                (ChcExpr::Bool(a), ChcExpr::Bool(b)) => {
                    if a != b {
                        return None;
                    }
                }
                (ChcExpr::Int(a), ChcExpr::Int(b)) => {
                    if a != b {
                        return None;
                    }
                }
                (ChcExpr::Real(a_num, a_den), ChcExpr::Real(b_num, b_den)) => {
                    if a_num != b_num || a_den != b_den {
                        return None;
                    }
                }
                (ChcExpr::Var(a), ChcExpr::Var(b)) => {
                    if a != b {
                        return None;
                    }
                }
                (ChcExpr::ConstArray(_ks, a), ChcExpr::ConstArray(_, b)) => {
                    todo.push((a.as_ref(), b.as_ref(), false));
                }
                (
                    ChcExpr::PredicateApp(name_a, id_a, args_a),
                    ChcExpr::PredicateApp(name_b, id_b, args_b),
                ) => {
                    if name_a != name_b || id_a != id_b || args_a.len() != args_b.len() {
                        return None;
                    }
                    push_child_pairs(&mut todo, args_a, args_b);
                }
                (
                    ChcExpr::FuncApp(name_a, sort_a, args_a),
                    ChcExpr::FuncApp(name_b, sort_b, args_b),
                ) => {
                    if name_a != name_b || sort_a != sort_b || args_a.len() != args_b.len() {
                        return None;
                    }
                    push_child_pairs(&mut todo, args_a, args_b);
                }
                (ChcExpr::Op(op_a, args_a), ChcExpr::Op(op_b, args_b)) => {
                    // Direct operator match.
                    if op_a == op_b && args_a.len() == args_b.len() {
                        push_child_pairs(&mut todo, args_a, args_b);
                        continue;
                    }

                    // Top-level signed match: strip one `not` when heads match after stripping.
                    if top {
                        if let Some((p2, i2)) = try_strip_top_not(pattern, instance) {
                            self.positive = false;
                            todo.push((p2, i2, false));
                            continue;
                        }
                    }

                    // Arithmetic equivalences.
                    if try_arith_equivalence(pattern, instance, &mut todo) {
                        continue;
                    }

                    return None;
                }
                _ => {
                    if pattern != instance {
                        return None;
                    }
                }
            }
        }

        let mut values = Vec::with_capacity(pattern_vars.len());
        for v in subst {
            values.push(v?);
        }
        Some((self.positive, values))
    }

    /// Match `instance` against `pattern`, requiring a positive match.
    pub(super) fn matches(
        &mut self,
        pattern: &ChcExpr,
        pattern_vars: &[ChcVar],
        instance: &ChcExpr,
    ) -> Option<Vec<i128>> {
        let (pos, subst_values) = self.matches_signed(pattern, pattern_vars, instance)?;
        if pos {
            Some(subst_values)
        } else {
            None
        }
    }

    fn try_linear_solve(
        &mut self,
        pattern: &ChcExpr,
        instance: &ChcExpr,
        var_to_idx: &FxHashMap<&str, usize>,
        subst: &mut [Option<i128>],
    ) -> Option<bool> {
        let (ChcExpr::Op(ChcOp::Add, pattern_args), ChcExpr::Int(target)) = (pattern, instance)
        else {
            return None;
        };
        if pattern_args.len() != 2 {
            return Some(false);
        }

        let (a0, a1) = (pattern_args[0].as_ref(), pattern_args[1].as_ref());
        let (var_idx, const_val) = match (
            pattern_var_index(a0, var_to_idx),
            pattern_var_index(a1, var_to_idx),
        ) {
            (Some(idx), None) => (idx, as_int(a1)?),
            (None, Some(idx)) => (idx, as_int(a0)?),
            _ => return None,
        };

        let Some(solved) = target.checked_sub(const_val) else {
            return Some(false);
        };

        match subst[var_idx] {
            Some(existing) if existing != solved => Some(false),
            Some(_) => Some(true),
            None => {
                subst[var_idx] = Some(solved);
                Some(true)
            }
        }
    }
}

fn as_int(expr: &ChcExpr) -> Option<i128> {
    match expr {
        ChcExpr::Int(n) => Some(*n),
        _ => None,
    }
}

fn pattern_var_index(expr: &ChcExpr, var_to_idx: &FxHashMap<&str, usize>) -> Option<usize> {
    match expr {
        ChcExpr::Var(v) => var_to_idx.get(v.name.as_str()).copied(),
        _ => None,
    }
}

fn push_child_pairs<'a>(
    todo: &mut Vec<(&'a ChcExpr, &'a ChcExpr, bool)>,
    a: &'a [Arc<ChcExpr>],
    b: &'a [Arc<ChcExpr>],
) {
    // Push in reverse so that the first argument is processed first (for determinism).
    for (x, y) in a.iter().zip(b.iter()).rev() {
        todo.push((x.as_ref(), y.as_ref(), false));
    }
}

fn strip_not(expr: &ChcExpr) -> Option<&ChcExpr> {
    let ChcExpr::Op(ChcOp::Not, args) = expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    Some(args[0].as_ref())
}

fn same_head(a: &ChcExpr, b: &ChcExpr) -> bool {
    match (a, b) {
        (ChcExpr::Op(op_a, args_a), ChcExpr::Op(op_b, args_b)) => {
            op_a == op_b && args_a.len() == args_b.len()
        }
        (
            ChcExpr::PredicateApp(name_a, id_a, args_a),
            ChcExpr::PredicateApp(name_b, id_b, args_b),
        ) => name_a == name_b && id_a == id_b && args_a.len() == args_b.len(),
        (ChcExpr::FuncApp(name_a, sort_a, args_a), ChcExpr::FuncApp(name_b, sort_b, args_b)) => {
            name_a == name_b && sort_a == sort_b && args_a.len() == args_b.len()
        }
        _ => false,
    }
}

fn try_strip_top_not<'a>(
    pattern: &'a ChcExpr,
    instance: &'a ChcExpr,
) -> Option<(&'a ChcExpr, &'a ChcExpr)> {
    let p_not = strip_not(pattern);
    let i_not = strip_not(instance);

    match (p_not, i_not) {
        (Some(_), Some(_)) => None, // exactly one side must have `not`
        (Some(p_inner), None) if same_head(p_inner, instance) => Some((p_inner, instance)),
        (None, Some(i_inner)) if same_head(pattern, i_inner) => Some((pattern, i_inner)),
        _ => None,
    }
}

fn try_arith_equivalence<'a>(
    pattern: &'a ChcExpr,
    instance: &'a ChcExpr,
    todo: &mut Vec<(&'a ChcExpr, &'a ChcExpr, bool)>,
) -> bool {
    // Eq/Ne equivalences.
    // x = y  ==  !(x != y)
    if let ChcExpr::Op(ChcOp::Eq, p_args) = pattern {
        if let Some(ChcExpr::Op(ChcOp::Ne, i_args)) = strip_not(instance) {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    if let Some(ChcExpr::Op(ChcOp::Ne, p_args)) = strip_not(pattern) {
        if let ChcExpr::Op(ChcOp::Eq, i_args) = instance {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    // x != y  ==  !(x = y)
    if let ChcExpr::Op(ChcOp::Ne, p_args) = pattern {
        if let Some(ChcExpr::Op(ChcOp::Eq, i_args)) = strip_not(instance) {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    if let Some(ChcExpr::Op(ChcOp::Eq, p_args)) = strip_not(pattern) {
        if let ChcExpr::Op(ChcOp::Ne, i_args) = instance {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    // x <= y  ==  !(x > y)
    if let ChcExpr::Op(ChcOp::Le, p_args) = pattern {
        if let Some(ChcExpr::Op(ChcOp::Gt, i_args)) = strip_not(instance) {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    if let Some(ChcExpr::Op(ChcOp::Gt, p_args)) = strip_not(pattern) {
        if let ChcExpr::Op(ChcOp::Le, i_args) = instance {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    // x >= y  ==  !(x < y)
    if let ChcExpr::Op(ChcOp::Ge, p_args) = pattern {
        if let Some(ChcExpr::Op(ChcOp::Lt, i_args)) = strip_not(instance) {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    if let Some(ChcExpr::Op(ChcOp::Lt, p_args)) = strip_not(pattern) {
        if let ChcExpr::Op(ChcOp::Ge, i_args) = instance {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    // x > y  ==  !(x <= y)
    if let ChcExpr::Op(ChcOp::Gt, p_args) = pattern {
        if let Some(ChcExpr::Op(ChcOp::Le, i_args)) = strip_not(instance) {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    if let Some(ChcExpr::Op(ChcOp::Le, p_args)) = strip_not(pattern) {
        if let ChcExpr::Op(ChcOp::Gt, i_args) = instance {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    // x < y  ==  !(x >= y)
    if let ChcExpr::Op(ChcOp::Lt, p_args) = pattern {
        if let Some(ChcExpr::Op(ChcOp::Ge, i_args)) = strip_not(instance) {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    if let Some(ChcExpr::Op(ChcOp::Ge, p_args)) = strip_not(pattern) {
        if let ChcExpr::Op(ChcOp::Lt, i_args) = instance {
            if p_args.len() == 2 && i_args.len() == 2 {
                todo.push((p_args[1].as_ref(), i_args[1].as_ref(), false));
                todo.push((p_args[0].as_ref(), i_args[0].as_ref(), false));
                return true;
            }
        }
    }

    false
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
