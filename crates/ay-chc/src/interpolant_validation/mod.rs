// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helpers for Craig interpolant validation.

use crate::expr_vars::expr_var_names;
use crate::smt::SmtResult;
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcOp, ChcSort};
use ay_core::kani_compat::DetHashSet as FxHashSet;

#[inline]
pub(crate) fn is_unsat_result(result: &SmtResult) -> bool {
    matches!(
        result,
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    )
}

/// Validate Craig interpolation properties for a candidate `interpolant`.
///
/// The caller supplies `check_sat` so this helper can be reused by modules that
/// use different SMT plumbing (`SmtContext` vs cached engine contexts).
pub(crate) fn is_valid_interpolant_with_check_sat<F>(
    a: &ChcExpr,
    b: &ChcExpr,
    interpolant: &ChcExpr,
    shared_vars: &FxHashSet<String>,
    mut check_sat: F,
) -> bool
where
    F: FnMut(&ChcExpr) -> SmtResult,
{
    let interpolant_vars: FxHashSet<String> = expr_var_names(interpolant);
    if !interpolant_vars.iter().all(|v| shared_vars.contains(v)) {
        return false;
    }

    // Check A |= I by proving UNSAT(A /\ !I).
    let a_and_not_i = ChcExpr::and(a.clone(), ChcExpr::not(interpolant.clone()));
    if !is_unsat_result(&check_sat(&a_and_not_i)) {
        return false;
    }

    // Check I /\ B is UNSAT.
    let i_and_b = ChcExpr::and(interpolant.clone(), b.clone());
    is_unsat_result(&check_sat(&i_and_b))
}

/// Validate that `inv` is a 1-inductive invariant for the transition system:
///   1. init ⇒ inv
///   2. inv ⇒ ¬query
///   3. inv ∧ T ⇒ inv' (1-inductiveness)
///
/// Returns `None` if valid, or `Some(check_name)` identifying the failing
/// check for diagnostics.
///
/// The caller provides `check_sat` so this can be reused across engines with
/// different SMT plumbing.
pub(crate) fn validate_inductive_invariant<F>(
    ts: &TransitionSystem,
    inv: &ChcExpr,
    mut check_sat: F,
) -> Option<&'static str>
where
    F: FnMut(&ChcExpr) -> SmtResult,
{
    // init ⇒ inv  <=>  UNSAT(init ∧ ¬inv)
    let init_and_not_inv = ChcExpr::and(ts.init.clone(), ChcExpr::not(inv.clone()));
    if !is_unsat_result(&check_sat(&init_and_not_inv)) {
        return Some("init => invariant");
    }

    // inv ⇒ ¬query  <=>  UNSAT(inv ∧ query)
    let inv_and_query = ChcExpr::and(inv.clone(), ts.query.clone());
    if !is_unsat_result(&check_sat(&inv_and_query)) {
        return Some("invariant => not query");
    }

    // 1-inductive: UNSAT(inv@0 ∧ T@0 ∧ ¬inv@1)
    let inv_t1 = TransitionSystem::version_expr(inv, ts.state_vars(), 1);
    let not_inv_t1 = ChcExpr::not(inv_t1);
    let transition = ts.transition_at(0);
    // A disjunctive invariant (IMC's reached set: init ∨ I1 ∨ …, each image
    // pinning its own constants) is checked one disjunct at a time: each
    // query then carries top-level units that the Search lane's equality
    // solving propagates through T, where the monolithic query hides them
    // under the disjunction. Every disjunct refuted ⇔ the whole query
    // refuted; any undecided disjunct falls back to the monolithic query.
    if let Some((disjuncts, rest)) = split_disjunctive(inv) {
        let mut all_refuted = true;
        for d in disjuncts {
            let mut parts = vec![d, transition.clone(), not_inv_t1.clone()];
            parts.extend(rest.iter().cloned());
            let result = check_sat(&ChcExpr::and_all(parts));
            if result.is_sat() {
                return Some("inductiveness");
            }
            if !is_unsat_result(&result) {
                all_refuted = false;
                break;
            }
        }
        if all_refuted {
            return None;
        }
    }
    let ind_check = ChcExpr::and(ChcExpr::and(inv.clone(), transition), not_inv_t1);
    if !is_unsat_result(&check_sat(&ind_check)) {
        return Some("inductiveness");
    }

    None
}

/// `(disjuncts, rest)` when `inv` is `D_1 ∨ … ∨ D_n` (nested `or`s flattened,
/// `n ≥ 2`), or `(D_1 ∨ … ∨ D_n) ∧ rest…`.
fn split_disjunctive(inv: &ChcExpr) -> Option<(Vec<ChcExpr>, Vec<ChcExpr>)> {
    fn flatten_or(e: &ChcExpr, out: &mut Vec<ChcExpr>) {
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            match e {
                ChcExpr::Op(ChcOp::Or, args) => stack.extend(args.iter().rev().map(|a| a.as_ref())),
                other => out.push(other.clone()),
            }
        }
    }
    let (disjunction, rest): (&ChcExpr, Vec<ChcExpr>) = match inv {
        ChcExpr::Op(ChcOp::Or, _) => (inv, Vec::new()),
        ChcExpr::Op(ChcOp::And, args) => {
            let pos = args
                .iter()
                .position(|a| matches!(a.as_ref(), ChcExpr::Op(ChcOp::Or, _)))?;
            let rest = args
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != pos)
                .map(|(_, a)| a.as_ref().clone())
                .collect();
            (args[pos].as_ref(), rest)
        }
        _ => return None,
    };
    let mut disjuncts = Vec::new();
    flatten_or(disjunction, &mut disjuncts);
    (disjuncts.len() >= 2).then_some((disjuncts, rest))
}

/// Flatten conjuncts for interpolation, expanding numeric equalities.
///
/// Collects conjuncts from an `And` tree, filtering trivial `true` literals.
/// Numeric equalities `a = b` are expanded to `(a ≤ b) ∧ (b ≤ a)` to improve
/// the linear interpolant generator's ability to eliminate variables (#966).
///
/// And-flattening delegates to the canonical `ChcExpr::collect_conjuncts_nontrivial`.
pub(crate) fn collect_conjuncts_for_interpolation(expr: &ChcExpr, out: &mut Vec<ChcExpr>) {
    for conj in expr.collect_conjuncts_nontrivial() {
        if let ChcExpr::Op(ChcOp::Eq, args) = &conj {
            if args.len() == 2 {
                let a = args[0].as_ref();
                let b = args[1].as_ref();
                let sort = a.sort();
                if sort == b.sort() && matches!(sort, ChcSort::Int | ChcSort::Real) {
                    out.push(ChcExpr::le(a.clone(), b.clone()));
                    out.push(ChcExpr::le(b.clone(), a.clone()));
                    continue;
                }
            }
        }
        out.push(conj);
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
