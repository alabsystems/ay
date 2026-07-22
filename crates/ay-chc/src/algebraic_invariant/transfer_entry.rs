// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::pdr::model::InvariantModel;
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Resolve a target pre_var's entry value through the transfer clause.
///
/// Returns the entry value as a ChcExpr in terms of ConstantDelta(0) vars
/// (which are the same at entry and current state) and constants.
#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_entry_value(
    target_var: &str,
    target_to_transfer: &FxHashMap<String, ChcExpr>,
    var_defs: &FxHashMap<String, ChcExpr>,
    source_subst: &[(ChcVar, ChcExpr)],
    _source_vars: &[ChcVar],
    _model: &InvariantModel,
    _source_pred_id: &PredicateId,
    source_constants: &FxHashMap<String, i128>,
    constant_target_vars: &FxHashSet<String>,
    pre_vars: &[String],
) -> Option<ChcExpr> {
    if constant_target_vars.contains(target_var) {
        return Some(ChcExpr::var(ChcVar::new(
            target_var.to_string(),
            ChcSort::Int,
        )));
    }

    let transfer_expr = target_to_transfer.get(target_var)?;
    let resolved = resolve_transfer_expr(transfer_expr, var_defs);
    let with_source_constants =
        substitute_source_constants(&resolved, source_subst, source_constants);
    let with_target_constants = replace_transfer_with_target_constants(
        &with_source_constants,
        pre_vars,
        constant_target_vars,
        target_to_transfer,
    );

    Some(with_target_constants)
}

/// Resolve a transfer clause expression through variable definitions.
fn resolve_transfer_expr(expr: &ChcExpr, var_defs: &FxHashMap<String, ChcExpr>) -> ChcExpr {
    match expr {
        ChcExpr::Var(v) => {
            if let Some(def) = var_defs.get(&v.name) {
                resolve_transfer_expr(def, var_defs)
            } else {
                expr.clone()
            }
        }
        _ => expr.clone(),
    }
}

/// Substitute transfer clause variables that correspond to source pred
/// variables with known constant values.
fn substitute_source_constants(
    expr: &ChcExpr,
    source_subst: &[(ChcVar, ChcExpr)],
    source_constants: &FxHashMap<String, i128>,
) -> ChcExpr {
    let mut transfer_to_source: FxHashMap<String, String> = FxHashMap::default();
    for (formal, actual) in source_subst {
        if let ChcExpr::Var(av) = actual {
            transfer_to_source.insert(av.name.clone(), formal.name.clone());
        }
    }

    let substitutions: Vec<(ChcVar, ChcExpr)> = expr
        .vars()
        .into_iter()
        .filter_map(|v| {
            let source_formal = transfer_to_source.get(&v.name)?;
            let val = source_constants.get(source_formal)?;
            Some((v, ChcExpr::int(*val)))
        })
        .collect();

    if substitutions.is_empty() {
        expr.clone()
    } else {
        expr.substitute(&substitutions)
    }
}

/// Replace transfer clause variables with corresponding target ConstantDelta(0)
/// variable names (since constant vars have the same value at entry and current).
fn replace_transfer_with_target_constants(
    expr: &ChcExpr,
    pre_vars: &[String],
    constant_target_vars: &FxHashSet<String>,
    target_to_transfer: &FxHashMap<String, ChcExpr>,
) -> ChcExpr {
    let mut transfer_to_target: Vec<(ChcVar, ChcExpr)> = Vec::new();
    for pre_var in pre_vars {
        if !constant_target_vars.contains(pre_var) {
            continue;
        }
        if let Some(ChcExpr::Var(tv)) = target_to_transfer.get(pre_var) {
            transfer_to_target.push((
                tv.clone(),
                ChcExpr::var(ChcVar::new(pre_var.clone(), ChcSort::Int)),
            ));
        }
    }

    if transfer_to_target.is_empty() {
        expr.clone()
    } else {
        expr.substitute(&transfer_to_target)
    }
}

/// Apply source invariant equalities to simplify an entry expression.
///
/// For example, if the source invariant says `2*A = C*(C+1)` and the entry
/// expression contains `2*A_transfer`, substitute to get `C*(C+1)` expressed
/// in target's ConstantDelta(0) vars.
#[allow(clippy::too_many_arguments)]
pub(super) fn apply_source_invariant_to_entry(
    entry_expr: &ChcExpr,
    model: &InvariantModel,
    source_pred_id: &PredicateId,
    source_subst: &[(ChcVar, ChcExpr)],
    constant_target_vars: &FxHashSet<String>,
    pre_vars: &[String],
    target_to_transfer: &FxHashMap<String, ChcExpr>,
    verbose: bool,
) -> Option<ChcExpr> {
    let source_interp = model.get(source_pred_id)?;
    let formula = &source_interp.formula;
    let equalities = extract_equalities(formula);

    for (lhs, rhs) in &equalities {
        let lhs_transfer = lhs.substitute(source_subst);
        let rhs_transfer = rhs.substitute(source_subst);

        if verbose {
            safe_eprintln!(
                "Algebraic conserved: source equality in transfer vars: {:?} = {:?}",
                lhs_transfer,
                rhs_transfer
            );
        }

        if entry_expr == &lhs_transfer {
            let result = replace_transfer_with_target_constants(
                &rhs_transfer,
                pre_vars,
                constant_target_vars,
                target_to_transfer,
            );
            return Some(result);
        }
    }

    let simplified = replace_transfer_with_target_constants(
        entry_expr,
        pre_vars,
        constant_target_vars,
        target_to_transfer,
    );
    if &simplified != entry_expr {
        Some(simplified)
    } else {
        None
    }
}

/// Extract (lhs, rhs) pairs from equality expressions.
fn extract_equalities(expr: &ChcExpr) -> Vec<(ChcExpr, ChcExpr)> {
    let mut result = Vec::new();
    match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            result.push(((*args[0]).clone(), (*args[1]).clone()));
        }
        ChcExpr::Op(ChcOp::And, args) => {
            for a in args {
                result.extend(extract_equalities(a));
            }
        }
        _ => {}
    }
    result
}

/// Compute which source predicate variables are constant (always the same value).
///
/// A variable is constant if: it has ConstantDelta(0) in the self-loop AND
/// the fact clause gives it a concrete init value.
pub(super) fn compute_source_constants(
    problem: &ChcProblem,
    source_pred_id: PredicateId,
    verbose: bool,
) -> FxHashMap<String, i128> {
    let mut constants = FxHashMap::default();

    let self_loop = problem.clauses().iter().find(|c| {
        c.head.predicate_id() == Some(source_pred_id)
            && c.body.predicates.len() == 1
            && c.body.predicates[0].0 == source_pred_id
    });
    let self_loop = match self_loop {
        Some(c) => c,
        None => return constants,
    };

    let (pre_vars, transition) = match super::extract_normalized_transition(self_loop) {
        Some(t) => t,
        None => return constants,
    };

    let system = match crate::recurrence::analyze_transition(&transition, &pre_vars) {
        Some(s) => s,
        None => return constants,
    };

    let init_values = match super::init::extract_init_values(problem, source_pred_id, &pre_vars) {
        Some(v) => v,
        None => return constants,
    };

    for (name, cf) in &system.solutions {
        if matches!(
            cf,
            crate::recurrence::ClosedForm::ConstantDelta { delta: 0 }
        ) {
            if let Some(&val) = init_values.get(name) {
                constants.insert(name.clone(), val);
                if verbose {
                    safe_eprintln!("Algebraic conserved: source constant {} = {}", name, val);
                }
            }
        }
    }

    constants
}
