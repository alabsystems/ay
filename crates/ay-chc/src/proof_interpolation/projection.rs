// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-based projection and expression utilities.

use super::*;

pub(super) fn try_mbp_projection(
    a_conj: &ChcExpr,
    shared_vars: &FxHashSet<String>,
    _smt: &mut SmtContext,
) -> Option<ChcExpr> {
    // Get all variables in A and find non-shared ones
    let a_vars = a_conj.vars();
    let non_shared: FxHashSet<String> = a_vars
        .iter()
        .filter(|v| !shared_vars.contains(&v.name))
        .map(|v| v.name.clone())
        .collect();

    if non_shared.is_empty() {
        // A already only mentions shared variables
        iuc_trace!("try_mbp_projection: A already uses only shared vars");
        return Some(a_conj.clone());
    }

    iuc_trace!(
        "try_mbp_projection: A has {} non-shared vars: {:?}",
        non_shared.len(),
        non_shared.iter().collect::<Vec<_>>()
    );

    // Flatten A into conjuncts
    let mut conjuncts = a_conj.collect_conjuncts();

    // Iteratively eliminate non-shared variables using equalities
    let mut remaining_non_shared = non_shared.clone();
    let mut max_iterations = non_shared.len() * 2; // Prevent infinite loops

    while !remaining_non_shared.is_empty() && max_iterations > 0 {
        max_iterations -= 1;

        // Find an equality that defines a non-shared variable in terms of other expressions
        let mut found_substitution = false;

        for i in 0..conjuncts.len() {
            if let Some((var_name, rhs)) =
                extract_equality_definition(&conjuncts[i], &remaining_non_shared)
            {
                // RHS must not mention the variable being eliminated
                let rhs_vars: FxHashSet<String> =
                    rhs.vars().iter().map(|v| v.name.clone()).collect();
                if rhs_vars.contains(&var_name) {
                    continue;
                }

                iuc_trace!("try_mbp_projection: eliminating {} = {}", var_name, rhs);

                // Substitute var_name -> rhs in all conjuncts (except the defining equality)
                let subst_map: FxHashMap<String, ChcExpr> =
                    [(var_name.clone(), rhs.clone())].into_iter().collect();
                let mut new_conjuncts = Vec::new();
                for (j, c) in conjuncts.iter().enumerate() {
                    if i == j {
                        // Skip the defining equality itself
                        continue;
                    }
                    let substituted = c.substitute_name_map(&subst_map);
                    let simplified = substituted.simplify_constants();
                    // Filter out trivially true constraints
                    if !matches!(simplified, ChcExpr::Bool(true)) {
                        new_conjuncts.push(simplified);
                    }
                }

                conjuncts = new_conjuncts;
                remaining_non_shared.remove(&var_name);
                found_substitution = true;
                break;
            }
        }

        if !found_substitution {
            // No more equalities to use for elimination
            break;
        }
    }

    // Check if we eliminated all non-shared variables
    let result_vars: FxHashSet<String> = conjuncts
        .iter()
        .flat_map(ChcExpr::vars)
        .map(|v| v.name)
        .collect();
    let final_non_shared: Vec<&String> = result_vars
        .iter()
        .filter(|v| !shared_vars.contains(*v))
        .collect();

    if final_non_shared.is_empty() {
        // Build result conjunction
        let result = ChcExpr::and_all(conjuncts);
        iuc_trace!("try_mbp_projection: success, projected = {}", result);
        Some(result)
    } else {
        // Equality substitution didn't eliminate all non-shared vars.
        // Try Fourier-Motzkin bound elimination as a fallback.
        iuc_trace!(
            "try_mbp_projection: trying inequality elimination for {} vars",
            final_non_shared.len()
        );

        let remaining_vars: FxHashSet<String> = final_non_shared.into_iter().cloned().collect();
        let remaining_var_names: FxHashSet<&str> =
            remaining_vars.iter().map(String::as_str).collect();

        if let Some(projected) = try_fourier_motzkin_elimination(&conjuncts, &remaining_var_names) {
            iuc_trace!("try_mbp_projection: F-M elimination succeeded");
            Some(projected)
        } else {
            iuc_trace!("try_mbp_projection: F-M elimination failed");
            None
        }
    }
}

/// Extract an equality definition: if expr is `var = rhs` or `rhs = var` where var is
/// in vars_to_eliminate, return Some((var_name, rhs)).
fn extract_equality_definition(
    expr: &ChcExpr,
    vars_to_eliminate: &FxHashSet<String>,
) -> Option<(String, ChcExpr)> {
    match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            let lhs = &args[0];
            let rhs = &args[1];

            // Check if LHS is a variable to eliminate
            if let ChcExpr::Var(v) = lhs.as_ref() {
                if vars_to_eliminate.contains(&v.name) {
                    return Some((v.name.clone(), rhs.as_ref().clone()));
                }
            }

            // Check if RHS is a variable to eliminate
            if let ChcExpr::Var(v) = rhs.as_ref() {
                if vars_to_eliminate.contains(&v.name) {
                    return Some((v.name.clone(), lhs.as_ref().clone()));
                }
            }

            None
        }
        _ => None,
    }
}

/// Check whether an expression is a linear arithmetic atom: a comparison
/// whose sub-expressions are linear terms (no `Var*Var`, no `Div`/`Mod`).
pub(super) fn is_linear_atom(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(op, args) if args.len() == 2 => {
            matches!(
                op,
                ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt | ChcOp::Eq
            ) && is_linear_term(&args[0])
                && is_linear_term(&args[1])
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => is_linear_atom(&args[0]),
        _ => false,
    }
}

/// Check whether a term is linear: constants and variables are linear,
/// `Add`/`Sub` preserve linearity, `Mul` requires at least one constant
/// operand, and `Neg` preserves linearity. `Div`/`Mod` are rejected
/// since they are piecewise/non-smooth and invalid for Farkas reasoning.
fn is_linear_term(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Int(_) | ChcExpr::Real(_, _) => true,
        ChcExpr::Var(v) => matches!(v.sort, ChcSort::Int | ChcSort::Real),
        ChcExpr::Op(ChcOp::Add | ChcOp::Sub, args) => args.iter().all(|a| is_linear_term(a)),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => is_linear_term(&args[0]),
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            // Linear if at least one operand is a constant
            let has_const = |e: &ChcExpr| matches!(e, ChcExpr::Int(_) | ChcExpr::Real(_, _));
            (has_const(&args[0]) && is_linear_term(&args[1]))
                || (has_const(&args[1]) && is_linear_term(&args[0]))
        }
        // Integer div/mod are not linear arithmetic and must not enter LIA-Farkas.
        ChcExpr::Op(ChcOp::Div | ChcOp::Mod, _) => false,
        _ => false,
    }
}

pub(super) fn flatten_constraints(constraints: &[ChcExpr]) -> Vec<ChcExpr> {
    let mut out = Vec::new();
    for c in constraints {
        c.collect_conjuncts_into(&mut out);
    }
    out.retain(|c| !matches!(c, ChcExpr::Bool(true)));
    out
}

pub(super) fn as_atom_and_value(expr: &ChcExpr) -> Option<(ChcExpr, bool)> {
    // Normalize to (atom, polarity) where polarity=true means assert atom,
    // and polarity=false means assert ¬atom.
    let mut polarity = true;
    let mut cur = expr;
    loop {
        match cur {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                polarity = !polarity;
                cur = args[0].as_ref();
            }
            _ => break,
        }
    }

    // Only accept linear arithmetic atoms (no Boolean structure).
    match cur {
        ChcExpr::Op(op, args) if args.len() == 2 => {
            if matches!(
                op,
                ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt | ChcOp::Eq
            ) {
                Some((cur.clone(), polarity))
            } else {
                None
            }
        }
        _ => None,
    }
}
