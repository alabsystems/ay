// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model verification and expression evaluation for the SMT backend.

use super::types::{ModelVerifyResult, SmtValue};
use crate::ChcExpr;
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::term::TermData;
use ay_core::{TermId, TermStore};

// Re-export the single source of truth for theory-atom routing from ay-core (#6881).
pub(crate) use ay_core::is_theory_atom;

/// Verify that a SAT model satisfies the original CHC expression.
///
/// Returns `Valid` if the expression evaluates to `true`, `Invalid` if it
/// evaluates to `false`, or `Indeterminate` if evaluation is incomplete
/// (predicates, arrays, uninterpreted functions, missing variables).
pub(super) fn verify_sat_model_strict(
    expr: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> ModelVerifyResult {
    match crate::expr::evaluate_expr(expr, model) {
        Some(SmtValue::Bool(true)) => ModelVerifyResult::Valid,
        Some(SmtValue::Bool(false)) => ModelVerifyResult::Invalid,
        _ => ModelVerifyResult::Indeterminate,
    }
}

/// Verify a SAT model against the original expression and, for explicit
/// mod/div formulas only, retry on the mod-eliminated form before rejecting.
pub(crate) fn verify_sat_model_strict_with_mod_retry(
    expr: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> ModelVerifyResult {
    let verify_result = verify_sat_model_strict(expr, model);
    if !matches!(verify_result, ModelVerifyResult::Invalid) || !expr.contains_mod_or_div() {
        return verify_result;
    }
    verify_sat_model_strict(&expr.eliminate_mod(), model)
}

/// Test helper: bool projection of strict model verification.
///
/// Returns `true` only for definitely valid models.
#[cfg(test)]
pub(super) fn verify_sat_model(expr: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> bool {
    matches!(
        verify_sat_model_strict(expr, model),
        ModelVerifyResult::Valid
    )
}

#[cfg(test)]
pub(super) fn verify_sat_model_conjunction<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
    model: &FxHashMap<String, SmtValue>,
) -> bool {
    matches!(
        verify_sat_model_conjunction_strict(exprs, model),
        ModelVerifyResult::Valid
    )
}

pub(crate) fn verify_sat_model_conjunction_strict<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
    model: &FxHashMap<String, SmtValue>,
) -> ModelVerifyResult {
    let mut saw_indeterminate = false;
    for expr in exprs {
        match verify_sat_model_strict(expr, model) {
            ModelVerifyResult::Valid => {}
            ModelVerifyResult::Invalid => return ModelVerifyResult::Invalid,
            ModelVerifyResult::Indeterminate => saw_indeterminate = true,
        }
    }

    if saw_indeterminate {
        ModelVerifyResult::Indeterminate
    } else {
        ModelVerifyResult::Valid
    }
}

/// Verify a conjunction strictly, retrying once on the mod-eliminated form
/// only when the first pass is `Invalid` and at least one conjunct contains an
/// explicit mod/div operator.
pub(crate) fn verify_sat_model_conjunction_strict_with_mod_retry<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
    model: &FxHashMap<String, SmtValue>,
) -> ModelVerifyResult {
    let exprs: Vec<&ChcExpr> = exprs.into_iter().collect();
    let verify_result = verify_sat_model_conjunction_strict(exprs.iter().copied(), model);
    if !matches!(verify_result, ModelVerifyResult::Invalid)
        || !exprs.iter().any(|expr| expr.contains_mod_or_div())
    {
        return verify_result;
    }

    let eliminated: Vec<ChcExpr> = exprs.iter().map(|expr| expr.eliminate_mod()).collect();
    verify_sat_model_conjunction_strict(eliminated.iter(), model)
}

/// Collect all theory atoms reachable from a set of roots.
///
/// Used for Craig interpolation origin tracking (#982): we record whether a conflict
/// literal came from the A-side background or the B-side assumptions.
pub(super) fn collect_theory_atoms_into(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
    out: &mut FxHashSet<TermId>,
) {
    let mut stack: Vec<TermId> = roots.into_iter().collect();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if is_theory_atom(terms, t) {
            out.insert(t);
        }
        match terms.get(t) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, then_br, else_br) => {
                stack.push(*c);
                stack.push(*then_br);
                stack.push(*else_br);
            }
            TermData::App(sym, args) => {
                if !args.is_empty()
                    && !matches!(
                        sym.name(),
                        "and" | "or" | "xor" | "=>" | "not" | "=" | "distinct" | "ite"
                    )
                {
                    out.extend(
                        args.iter()
                            .copied()
                            .filter(|&arg| terms.sort(arg) == &ay_core::Sort::Bool),
                    );
                }
                stack.extend(args.iter().copied());
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            // Unknown TermData variant; skip (no children to process) (#6091).
            _ => {}
        }
    }
}
