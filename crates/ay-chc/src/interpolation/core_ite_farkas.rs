// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D11: Core-guided ITE-normalized Farkas interpolation.
//!
//! When the standard Farkas pipeline fails on mixed Bool+LIA formulas
//! (because `walk_linear_expr` rejects ITE terms), this module case-splits
//! on ITE conditions so that each case becomes pure LIA, then delegates
//! to the existing Farkas/bound/transitivity infrastructure.
//!
//! Design: the development design notes

use crate::expr::dag::Step;
use crate::farkas::compute_interpolant_until as farkas_interpolant_until;
use crate::interpolation::heuristics::{
    compute_bound_interpolant, compute_transitivity_interpolant,
};
use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::time::Instant;
use std::sync::Arc;
use tracing::{debug, info};

/// Maximum case-split budget: 2^n ≤ this value.
const ITE_CASE_BUDGET: usize = 64;
/// The most distinct ITE conditions whose 2^n case split fits
/// [`ITE_CASE_BUDGET`].
const MAX_ITE_CONDITIONS: usize = ITE_CASE_BUDGET.ilog2() as usize;

/// Compute interpolant by case-splitting on ITE conditions.
///
/// Returns `Some(I)` where `vars(I) ⊆ shared_vars`, or `None` if no ITE
/// conditions are found, the budget is exceeded, or per-case interpolation
/// fails for all cases.
pub(crate) fn compute_ite_farkas_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    compute_ite_farkas_interpolant_until(a_constraints, b_constraints, shared_vars, None)
}

/// Deadline-aware variant (inc-19): up to 64 case splits each run the full
/// Farkas strategy cascade; the caller's wall-clock deadline bounds the loop
/// and each per-case Farkas attempt. `None` keeps legacy behavior.
pub(crate) fn compute_ite_farkas_interpolant_until(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    deadline: Option<Instant>,
) -> Option<ChcExpr> {
    let _census_role = crate::smt::lane::ScopedCensusRole::set("interp");
    // 1. Collect the distinct ITE conditions of all constraints (first
    // occurrences, in tree preorder), stopping once the case budget is
    // exceeded: no further condition can bring the count back under it.
    let Some(conditions) = collect_ite_conditions(
        a_constraints.iter().chain(b_constraints.iter()),
        MAX_ITE_CONDITIONS,
    ) else {
        info!(
            event = "chc_ite_farkas_skip",
            reason = "budget_exceeded",
            conditions = MAX_ITE_CONDITIONS + 1,
        );
        return None;
    };

    if conditions.is_empty() {
        return None;
    }
    let n = conditions.len();

    // 2. Classify each condition's variable ownership
    let a_vars: FxHashSet<String> = a_constraints
        .iter()
        .flat_map(|e| e.vars().into_iter().map(|v| v.name))
        .collect();
    let b_vars: FxHashSet<String> = b_constraints
        .iter()
        .flat_map(|e| e.vars().into_iter().map(|v| v.name))
        .collect();

    // 3. Enumerate all 2^n cases and compute per-case interpolants
    let num_cases = 1usize << n;
    let mut case_interpolants: Vec<Option<ChcExpr>> = Vec::with_capacity(num_cases);

    for case_idx in 0..num_cases {
        if super::deadline_expired(deadline) {
            info!(
                event = "chc_ite_farkas_skip",
                reason = "deadline_expired",
                case_idx
            );
            return None;
        }
        let assignment: Vec<bool> = (0..n).map(|bit| (case_idx >> bit) & 1 == 1).collect();

        let a_subst = substitute_ite_case(a_constraints, &conditions, &assignment);
        let b_subst = substitute_ite_case(b_constraints, &conditions, &assignment);

        // Try Farkas first, then bound, then transitivity
        let interp = farkas_interpolant_until(&a_subst, &b_subst, shared_vars, deadline)
            .or_else(|| compute_bound_interpolant(&a_subst, &b_subst, shared_vars))
            .or_else(|| compute_transitivity_interpolant(&a_subst, &b_subst, shared_vars));

        if let Some(ref i) = interp {
            debug!(
                event = "chc_ite_farkas_case_ok",
                case_idx,
                interp_vars = i.vars().len() as u64,
            );
        } else {
            debug!(event = "chc_ite_farkas_case_fail", case_idx,);
        }
        case_interpolants.push(interp);
    }

    // 4. Combine using Craig algebra
    let result = combine_interpolants(
        &conditions,
        &case_interpolants,
        shared_vars,
        &a_vars,
        &b_vars,
    );

    if let Some(ref interp) = result {
        let interp_vars: FxHashSet<String> = interp.vars().into_iter().map(|v| v.name).collect();
        if !interp_vars.iter().all(|v| shared_vars.contains(v)) {
            info!(
                event = "chc_ite_farkas_locality_failure",
                non_shared = interp_vars.difference(shared_vars).count(),
            );
            return None;
        }
    }

    result
}

/// The distinct ITE conditions (`args[0]` of `ite` nodes reached through
/// `Op` nodes) of `exprs`, in the order of their first occurrence in a
/// recursive preorder tree walk, or `None` once more than `cap` are found.
///
/// DAG time: a shared node (same `Arc`) is walked once, which collects
/// exactly what the tree walk collects after deduplication (its first
/// visit already reached every condition below it). The LRA-Lin `let`
/// DAGs (cav12 transmitter.2: 1.8e12 tree nodes) kept IMC's interpolation
/// in this walk for the whole run.
fn collect_ite_conditions<'a>(
    exprs: impl Iterator<Item = &'a ChcExpr>,
    cap: usize,
) -> Option<Vec<ChcExpr>> {
    let mut seen = FxHashSet::default();
    let mut conditions = Vec::new();
    for expr in exprs {
        let complete = crate::expr::dag::walk_distinct_preorder(expr, |node| match node {
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                if seen.insert(args[0].as_ref().clone()) {
                    conditions.push(args[0].as_ref().clone());
                    if conditions.len() > cap {
                        return Step::Stop;
                    }
                }
                Step::Descend
            }
            ChcExpr::Op(..) => Step::Descend,
            _ => Step::Skip,
        });
        if !complete {
            return None;
        }
    }
    Some(conditions)
}

/// Substitute ITE conditions with truth values, add condition guards, and simplify.
fn substitute_ite_case(
    constraints: &[ChcExpr],
    conditions: &[ChcExpr],
    assignment: &[bool],
) -> Vec<ChcExpr> {
    let mut result: Vec<ChcExpr> = constraints
        .iter()
        .map(|expr| {
            let mut e = expr.clone();
            for (cond, &val) in conditions.iter().zip(assignment.iter()) {
                e = substitute_ite_condition(&e, cond, val);
            }
            e.simplify_constants()
        })
        .collect();

    // CRITICAL: Add condition guards as explicit constraints (D11 step 4b).
    // Without these, a model of the substituted constraints might assign
    // the ITE condition to the opposite truth value, making the original
    // formula evaluate the ITE to the wrong branch.
    for (cond, &val) in conditions.iter().zip(assignment.iter()) {
        if val {
            result.push(cond.clone());
        } else {
            result.push(ChcExpr::not(cond.clone()));
        }
    }
    result
}

/// Replace `ite(c, t, e)` with `t` (if val=true) or `e` (if val=false)
/// for all occurrences where the condition matches `cond`.
///
/// Each distinct node (same `Arc`) is rewritten once and its result shared,
/// so a `let` DAG is rewritten in DAG time; the result is structurally the
/// tree rewrite's.
fn substitute_ite_condition(expr: &ChcExpr, cond: &ChcExpr, val: bool) -> ChcExpr {
    let mut memo: FxHashMap<*const ChcExpr, Arc<ChcExpr>> = FxHashMap::default();
    substitute_ite_condition_memo(expr, cond, val, &mut memo)
}

fn substitute_ite_condition_arc(
    arg: &Arc<ChcExpr>,
    cond: &ChcExpr,
    val: bool,
    memo: &mut FxHashMap<*const ChcExpr, Arc<ChcExpr>>,
) -> Arc<ChcExpr> {
    let key = Arc::as_ptr(arg);
    if let Some(done) = memo.get(&key) {
        return Arc::clone(done);
    }
    let rewritten: Arc<ChcExpr> =
        crate::expr::maybe_grow_expr_stack(|| substitute_ite_condition_memo(arg, cond, val, memo))
            .into();
    memo.insert(key, Arc::clone(&rewritten));
    rewritten
}

fn substitute_ite_condition_memo(
    expr: &ChcExpr,
    cond: &ChcExpr,
    val: bool,
    memo: &mut FxHashMap<*const ChcExpr, Arc<ChcExpr>>,
) -> ChcExpr {
    match expr {
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            if args[0].as_ref() == cond {
                // Match: the chosen branch (may contain nested ITEs)
                let branch = if val { &args[1] } else { &args[2] };
                substitute_ite_condition_arc(branch, cond, val, memo)
                    .as_ref()
                    .clone()
            } else {
                // Non-matching ITE: recurse into all children
                let new_args: Vec<_> = args
                    .iter()
                    .map(|a| substitute_ite_condition_arc(a, cond, val, memo))
                    .collect();
                ChcExpr::Op(ChcOp::Ite, new_args)
            }
        }
        ChcExpr::Op(op, args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| substitute_ite_condition_arc(a, cond, val, memo))
                .collect();
            ChcExpr::Op(*op, new_args)
        }
        // Leaves (Int, Bool, Var, etc.) are unchanged
        _ => expr.clone(),
    }
}

/// Combine per-case interpolants using Craig algebra rules.
///
/// The case_interpolants array is indexed by case_idx where bit k of case_idx
/// corresponds to conditions[k] (bit 0 = LSB = conditions[0]).
///
/// For each condition c with truth-value cases (I_true, I_false):
/// - c is shared:    `(c ∧ I_true) ∨ (¬c ∧ I_false)`
/// - c is A-private: `I_true ∨ I_false`
/// - c is B-private: `I_true ∧ I_false`
///
/// If ANY case has no interpolant, returns None (soundness requirement:
/// all case splits of A ∧ B UNSAT must produce interpolants).
fn combine_interpolants(
    conditions: &[ChcExpr],
    case_interpolants: &[Option<ChcExpr>],
    shared_vars: &FxHashSet<String>,
    a_vars: &FxHashSet<String>,
    b_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    let n = conditions.len();
    if n == 0 {
        return case_interpolants.first().and_then(Clone::clone);
    }

    // All cases must have interpolants for sound combination
    if case_interpolants.iter().any(Option::is_none) {
        info!(
            event = "chc_ite_farkas_incomplete_cases",
            total = case_interpolants.len() as u64,
            missing = case_interpolants.iter().filter(|c| c.is_none()).count() as u64,
        );
        return None;
    }

    // Recursively combine from condition 0 to n-1.
    // At each level, group cases by bit `cond_idx`:
    //   false group = cases where bit cond_idx is 0
    //   true group  = cases where bit cond_idx is 1
    combine_by_condition(
        case_interpolants,
        conditions,
        0,
        n,
        shared_vars,
        a_vars,
        b_vars,
    )
}

/// Recursively combine interpolants by splitting on condition `cond_idx`.
///
/// `interps` is a slice of case interpolants where cases differ only in
/// conditions[cond_idx..n]. At each level, we split into groups where
/// bit `cond_idx` is 0 vs 1, recursively combine each group over
/// conditions[cond_idx+1..n], then apply the Craig algebra rule for
/// conditions[cond_idx].
fn combine_by_condition(
    interps: &[Option<ChcExpr>],
    conditions: &[ChcExpr],
    cond_idx: usize,
    n: usize,
    shared_vars: &FxHashSet<String>,
    a_vars: &FxHashSet<String>,
    b_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    if interps.len() == 1 {
        return interps[0].clone();
    }
    if cond_idx >= n {
        return interps.first().and_then(Clone::clone);
    }

    // Split by bit `cond_idx`:
    // Cases are ordered by case_idx where bit k = conditions[k].
    // Bit cond_idx alternates every 2^cond_idx entries.
    let stride = 1usize << cond_idx;
    let block = stride * 2;
    let mut false_group = Vec::new();
    let mut true_group = Vec::new();

    let mut i = 0;
    while i < interps.len() {
        // First `stride` entries in each block have bit cond_idx = 0
        for j in 0..stride.min(interps.len() - i) {
            false_group.push(interps[i + j].clone());
        }
        i += stride;
        // Next `stride` entries have bit cond_idx = 1
        for j in 0..stride.min(interps.len().saturating_sub(i)) {
            true_group.push(interps[i + j].clone());
        }
        i += stride;
        let _ = block; // suppress unused warning
    }

    let i_false = combine_by_condition(
        &false_group,
        conditions,
        cond_idx + 1,
        n,
        shared_vars,
        a_vars,
        b_vars,
    );
    let i_true = combine_by_condition(
        &true_group,
        conditions,
        cond_idx + 1,
        n,
        shared_vars,
        a_vars,
        b_vars,
    );

    // Combine I_false and I_true based on condition ownership
    let cond = &conditions[cond_idx];
    let cond_vars: FxHashSet<String> = cond.vars().into_iter().map(|v| v.name).collect();

    let is_a_only = cond_vars
        .iter()
        .all(|v| a_vars.contains(v) && !b_vars.contains(v));
    let is_b_only = cond_vars
        .iter()
        .all(|v| b_vars.contains(v) && !a_vars.contains(v));

    match (i_false, i_true) {
        (Some(i_f), Some(i_t)) => {
            if is_b_only {
                // c is B-private: I = I_true ∧ I_false
                Some(ChcExpr::and(i_t, i_f))
            } else if is_a_only {
                // c is A-private: I = I_true ∨ I_false
                Some(ChcExpr::or(i_t, i_f))
            } else {
                // c is shared (or mixed): I = (c ∧ I_true) ∨ (¬c ∧ I_false)
                Some(ChcExpr::or(
                    ChcExpr::and(cond.clone(), i_t),
                    ChcExpr::and(ChcExpr::not(cond.clone()), i_f),
                ))
            }
        }
        // If either side is None, the combination is incomplete — return None.
        // Both case splits should be UNSAT (since A ∧ B is UNSAT), but if
        // Farkas/bound/transitivity can't handle one case, we can't produce
        // a sound combined interpolant.
        _ => None,
    }
}

#[cfg(test)]
#[path = "core_ite_farkas_tests.rs"]
mod tests;
