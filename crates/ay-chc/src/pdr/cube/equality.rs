// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality extraction, propagation, and model augmentation.
//!
//! Contains functions for extracting equality constraints from expressions,
//! propagating derived values through fixpoint iteration, and augmenting
//! SMT models with inferred values.

use super::contradiction::collect_equalities_for_point_check;
use super::eval::try_eval_const;
use super::PointCubeUnionFind;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use num_traits::One;
use std::sync::Arc;

/// Extract equalities and linear relations, then propagate values.
///
/// Scans an expression for equality constraints like `(= x 5)` or `(= x (+ y 1))`
/// and uses them to derive variable values through fixpoint iteration.
pub(in crate::pdr) fn extract_equalities_and_propagate(expr: &ChcExpr) -> FxHashMap<String, i128> {
    let mut values = FxHashMap::default();
    let mut relations: Vec<(String, String, i128)> = Vec::new(); // (x, y, c) means x = y + c

    extract_equalities_with_relations(expr, &mut values, &mut relations);

    // Propagate values through relations until fixpoint
    let mut changed = true;
    while changed {
        changed = false;
        for (x, y, c) in &relations {
            // If we know y, compute x = y + c
            if let Some(&y_val) = values.get(y) {
                if let Some(x_val) = y_val.checked_add(*c) {
                    if !values.contains_key(x) {
                        values.insert(x.clone(), x_val);
                        changed = true;
                    }
                }
            }
            // If we know x, compute y = x - c
            if let Some(&x_val) = values.get(x) {
                if let Some(y_val) = x_val.checked_sub(*c) {
                    if !values.contains_key(y) {
                        values.insert(y.clone(), y_val);
                        changed = true;
                    }
                }
            }
        }
    }
    // Postcondition: fixpoint reached — no relation can derive a new value
    debug_assert!(
        {
            let mut stable = true;
            for (x, y, c) in &relations {
                if let Some(&y_val) = values.get(y) {
                    if let Some(x_val) = y_val.checked_add(*c) {
                        if !values.contains_key(x) {
                            stable = false;
                            break;
                        }
                        // Consistency: if x already has a value, it must agree
                        if let Some(&existing) = values.get(x) {
                            if existing != x_val {
                                stable = false;
                                break;
                            }
                        }
                    }
                }
            }
            stable
        },
        "BUG: extract_equalities_and_propagate did not reach fixpoint",
    );
    values
}

/// Extract equalities/relations and propagate them, seeding with known values.
pub(in crate::pdr) fn extract_equalities_and_propagate_with_seed(
    expr: &ChcExpr,
    seed_values: &FxHashMap<String, i128>,
) -> FxHashMap<String, i128> {
    let mut values = seed_values.clone();
    let mut relations: Vec<(String, String, i128)> = Vec::new(); // (x, y, c) means x = y + c

    extract_equalities_with_relations(expr, &mut values, &mut relations);

    // Propagate values through relations until fixpoint
    let mut changed = true;
    while changed {
        changed = false;
        for (x, y, c) in &relations {
            // If we know y, compute x = y + c
            if let Some(&y_val) = values.get(y) {
                if let Some(x_val) = y_val.checked_add(*c) {
                    if !values.contains_key(x) {
                        values.insert(x.clone(), x_val);
                        changed = true;
                    }
                }
            }
            // If we know x, compute y = x - c
            if let Some(&x_val) = values.get(x) {
                if let Some(y_val) = x_val.checked_sub(*c) {
                    if !values.contains_key(y) {
                        values.insert(y.clone(), y_val);
                        changed = true;
                    }
                }
            }
        }
    }
    values
}

/// Internal helper that extracts both direct equalities and linear relations.
pub(in crate::pdr) fn extract_equalities_with_relations(
    expr: &ChcExpr,
    values: &mut FxHashMap<String, i128>,
    relations: &mut Vec<(String, String, i128)>,
) {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::And, args) => {
            for arg in args {
                extract_equalities_with_relations(arg, values, relations);
            }
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            // Check for (= var constant) or (= constant var)
            // Use try_eval_const to handle expressions like (- 2)
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), rhs) if try_eval_const(rhs).is_some() => {
                    if let Some(rhs_value) = try_eval_const(rhs) {
                        values.insert(v.name.clone(), rhs_value);
                    }
                }
                (lhs, ChcExpr::Var(v)) if try_eval_const(lhs).is_some() => {
                    if let Some(lhs_value) = try_eval_const(lhs) {
                        values.insert(v.name.clone(), lhs_value);
                    }
                }
                // Handle (= x y) - direct equality relation
                (ChcExpr::Var(x), ChcExpr::Var(y)) => {
                    relations.push((x.name.clone(), y.name.clone(), 0));
                }
                // Handle (= (+ y c) n) (and symmetric) - solve for y.
                // Now supports c being any constant expression like (- 2)
                (ChcExpr::Op(ChcOp::Add, add_args), rhs) if add_args.len() == 2 => {
                    if let Some(n) = try_eval_const(rhs) {
                        // Try both orderings: (var, const) and (const, var)
                        let (a0, a1) = (add_args[0].as_ref(), add_args[1].as_ref());
                        if let ChcExpr::Var(y) = a0 {
                            if let Some(c) = try_eval_const(a1) {
                                if let Some(val) = n.checked_sub(c) {
                                    values.insert(y.name.clone(), val);
                                }
                            }
                        } else if let ChcExpr::Var(y) = a1 {
                            if let Some(c) = try_eval_const(a0) {
                                if let Some(val) = n.checked_sub(c) {
                                    values.insert(y.name.clone(), val);
                                }
                            }
                        }
                    }
                }
                (lhs, ChcExpr::Op(ChcOp::Add, add_args)) if add_args.len() == 2 => {
                    if let Some(n) = try_eval_const(lhs) {
                        let (a0, a1) = (add_args[0].as_ref(), add_args[1].as_ref());
                        if let ChcExpr::Var(y) = a0 {
                            if let Some(c) = try_eval_const(a1) {
                                if let Some(val) = n.checked_sub(c) {
                                    values.insert(y.name.clone(), val);
                                }
                            }
                        } else if let ChcExpr::Var(y) = a1 {
                            if let Some(c) = try_eval_const(a0) {
                                if let Some(val) = n.checked_sub(c) {
                                    values.insert(y.name.clone(), val);
                                }
                            }
                        }
                    }
                }
                // Handle (= x (+ y c)) or (= x (+ c y)) - linear relation
                (ChcExpr::Var(x), ChcExpr::Op(ChcOp::Add, add_args)) if add_args.len() == 2 => {
                    let (a0, a1) = (add_args[0].as_ref(), add_args[1].as_ref());
                    if let ChcExpr::Var(y) = a0 {
                        if let Some(c) = try_eval_const(a1) {
                            relations.push((x.name.clone(), y.name.clone(), c));
                        }
                    } else if let ChcExpr::Var(y) = a1 {
                        if let Some(c) = try_eval_const(a0) {
                            relations.push((x.name.clone(), y.name.clone(), c));
                        }
                    }
                }
                (ChcExpr::Op(ChcOp::Add, add_args), ChcExpr::Var(x)) if add_args.len() == 2 => {
                    let (a0, a1) = (add_args[0].as_ref(), add_args[1].as_ref());
                    if let ChcExpr::Var(y) = a0 {
                        if let Some(c) = try_eval_const(a1) {
                            relations.push((x.name.clone(), y.name.clone(), c));
                        }
                    } else if let ChcExpr::Var(y) = a1 {
                        if let Some(c) = try_eval_const(a0) {
                            relations.push((x.name.clone(), y.name.clone(), c));
                        }
                    }
                }
                // Handle (= x (- y c)) - subtraction
                (ChcExpr::Var(x), ChcExpr::Op(ChcOp::Sub, sub_args)) if sub_args.len() == 2 => {
                    if let ChcExpr::Var(y) = sub_args[0].as_ref() {
                        if let Some(c) = try_eval_const(&sub_args[1]) {
                            // x = y - c, equivalent to x = y + (-c)
                            if let Some(neg_c) = c.checked_neg() {
                                relations.push((x.name.clone(), y.name.clone(), neg_c));
                            }
                        }
                    }
                }
                // Handle (= (- y c) n) (and symmetric) - solve for y.
                (ChcExpr::Op(ChcOp::Sub, sub_args), rhs) if sub_args.len() == 2 => {
                    if let Some(n) = try_eval_const(rhs) {
                        if let ChcExpr::Var(y) = sub_args[0].as_ref() {
                            if let Some(c) = try_eval_const(&sub_args[1]) {
                                // y - c = n => y = n + c
                                if let Some(val) = n.checked_add(c) {
                                    values.insert(y.name.clone(), val);
                                }
                            }
                        }
                    }
                }
                (lhs, ChcExpr::Op(ChcOp::Sub, sub_args)) if sub_args.len() == 2 => {
                    if let Some(n) = try_eval_const(lhs) {
                        if let ChcExpr::Var(y) = sub_args[0].as_ref() {
                            if let Some(c) = try_eval_const(&sub_args[1]) {
                                // n = y - c => y = n + c
                                if let Some(val) = n.checked_add(c) {
                                    values.insert(y.name.clone(), val);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        _ => {}
    });
}

/// Collect equalities from an expression into a list of (lhs, rhs) pairs.
pub(in crate::pdr) fn collect_equalities(
    expr: &ChcExpr,
    out: &mut Vec<(Arc<ChcExpr>, Arc<ChcExpr>)>,
) {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::And | ChcOp::Or, args) => {
            for a in args {
                collect_equalities(a, out);
            }
        }
        ChcExpr::Op(ChcOp::Not, args) => {
            if let Some(a) = args.first() {
                collect_equalities(a, out);
            }
        }
        ChcExpr::Op(ChcOp::Implies | ChcOp::Iff, args) => {
            if let Some(a) = args.first() {
                collect_equalities(a, out);
            }
            if let Some(b) = args.get(1) {
                collect_equalities(b, out);
            }
        }
        ChcExpr::Op(ChcOp::Ite, args) => {
            for a in args {
                collect_equalities(a, out);
            }
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            out.push((args[0].clone(), args[1].clone()));
        }
        ChcExpr::Op(_, args) => {
            for a in args {
                collect_equalities(a, out);
            }
        }
        ChcExpr::PredicateApp(_, _, args) => {
            for a in args {
                collect_equalities(a, out);
            }
        }
        ChcExpr::FuncApp(_, _, args) => {
            for a in args {
                collect_equalities(a, out);
            }
        }
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Real(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::ConstArray(_, _) => {}
    });
}

/// Augment a model by evaluating equalities and propagating values.
///
/// Iterates to a fixpoint since derived values may enable more evaluations.
pub(in crate::pdr) fn augment_model_from_eval_equalities(
    expr: &ChcExpr,
    model: &mut FxHashMap<String, SmtValue>,
) {
    let mut equalities: Vec<(Arc<ChcExpr>, Arc<ChcExpr>)> = Vec::new();
    collect_equalities(expr, &mut equalities);

    // Iterate to a fixpoint since derived values may enable more evaluations.
    let mut converged = false;
    for _ in 0..8 {
        let mut changed = false;
        for (lhs, rhs) in &equalities {
            match (lhs.as_ref(), rhs.as_ref()) {
                (ChcExpr::Var(v), rhs_expr) if !model.contains_key(&v.name) => {
                    if let Some(val) = crate::expr::evaluate_expr(rhs_expr, model) {
                        model.insert(v.name.clone(), val);
                        changed = true;
                    }
                }
                (lhs_expr, ChcExpr::Var(v)) if !model.contains_key(&v.name) => {
                    if let Some(val) = crate::expr::evaluate_expr(lhs_expr, model) {
                        model.insert(v.name.clone(), val);
                        changed = true;
                    }
                }
                _ => {}
            }
        }
        if !changed {
            converged = true;
            break;
        }
    }
    // Warn if fixpoint iteration did not converge within 8 rounds.
    // Not a hard invariant (model is still usable), but signals
    // formulas with deep equality chains that may need a larger bound.
    debug_assert!(
        converged || equalities.is_empty(),
        "BUG: augment_model_from_eval_equalities did not converge in 8 rounds \
         ({} equalities, {} model entries)",
        equalities.len(),
        model.len(),
    );
}

/// Extract equalities from a formula and populate an SMT model.
///
/// Used when SMT solver returns empty model for satisfiable formula.
pub(in crate::pdr) fn extract_equalities_from_formula(
    expr: &ChcExpr,
    model: &mut FxHashMap<String, SmtValue>,
) {
    let int_values = extract_equalities_and_propagate(expr);
    for (name, value) in int_values {
        model.entry(name).or_insert(SmtValue::Int(value));
    }

    // Phase-2 BigInt escape: recover direct `var = <constant tree>` conjuncts
    // whose fold exceeds i128 (parser Horner encodings of beyond-i128
    // literals). The i128 propagation pass above abstains on them; the exact
    // BigInt fold recovers the witness value losslessly (Int-if-fits via the
    // canonical constructor). Model-preserving: existing assignments win.
    extract_bigint_equalities_from_conjuncts(expr, model);

    // Also recover non-arithmetic equalities that become evaluable after the
    // integer pass, e.g. `p = mkPair(1, 10)` followed by `old = target(p)`.
    // This is intentionally model-preserving: existing solver assignments win.
    augment_model_from_eval_equalities(expr, model);
}

/// Recover `var = <variable-free constant tree>` bindings via the exact
/// BigInt evaluator ([`crate::expr::eval_int_big`] aborts on any variable, so
/// only genuinely constant right-hand sides bind — never a guess).
fn extract_bigint_equalities_from_conjuncts(
    expr: &ChcExpr,
    model: &mut FxHashMap<String, SmtValue>,
) {
    let empty: FxHashMap<String, SmtValue> = FxHashMap::default();
    for conjunct in expr.collect_conjuncts() {
        let ChcExpr::Op(ChcOp::Eq, args) = &conjunct else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let (var, rhs) = match (args[0].as_ref(), args[1].as_ref()) {
            (ChcExpr::Var(v), rhs) => (v, rhs),
            (lhs, ChcExpr::Var(v)) => (v, lhs),
            _ => continue,
        };
        if var.sort != ChcSort::Int || model.contains_key(&var.name) {
            continue;
        }
        if let Some(value) = crate::expr::eval_int_big(rhs, &empty) {
            model.insert(var.name.clone(), SmtValue::int_from_bigint(value));
        }
    }
}

/// Augment a model with values derived from equality constraints.
pub(in crate::pdr) fn augment_model_from_equalities(
    constraint: &ChcExpr,
    model: &mut FxHashMap<String, SmtValue>,
) {
    // Precondition: capture original model keys to verify they are not overwritten
    #[cfg(debug_assertions)]
    let original_keys: Vec<String> = model.keys().cloned().collect();
    #[cfg(debug_assertions)]
    let original_values: FxHashMap<String, SmtValue> = model.clone();

    let mut seed = FxHashMap::default();
    for (name, value) in model.iter() {
        let Some(int_value) = (match value {
            SmtValue::Int(n) => Some(*n),
            SmtValue::BitVec(n, _w) => i128::try_from(*n).ok(),
            SmtValue::BigBitVec(n, _w) => num_traits::ToPrimitive::to_i128(n.as_ref()),
            SmtValue::Real(r) => {
                // Use integer part if denominator is 1
                if r.denom().is_one() {
                    use num_traits::ToPrimitive;
                    r.numer().to_i64().map(i128::from)
                } else {
                    None
                }
            }
            // Beyond-i128 witnesses: skip the heuristic seed (fail-closed
            // abstention, never truncate) — this is an i128 boundary.
            SmtValue::BigInt(_)
            | SmtValue::Bool(_)
            | SmtValue::Opaque(_)
            | SmtValue::ConstArray(_)
            | SmtValue::ArrayMap { .. }
            | SmtValue::Datatype(..) => None,
        }) else {
            continue;
        };
        seed.insert(name.clone(), int_value);
    }

    let inferred = extract_equalities_and_propagate_with_seed(constraint, &seed);
    for (name, value) in inferred {
        model.entry(name).or_insert(SmtValue::Int(value));
    }

    // Best-effort: propagate simple arithmetic definitions like `E = A + C` when the
    // SMT backend model doesn't include the derived variables (common for CHC transition-local
    // variables used only as predicate arguments).
    augment_model_from_eval_equalities(constraint, model);

    // Postcondition: original model entries must not be overwritten
    #[cfg(debug_assertions)]
    for key in &original_keys {
        debug_assert!(
            model.get(key) == original_values.get(key),
            "BUG: augment_model_from_equalities overwrote original model entry '{key}'",
        );
    }
}

/// Check if a cube is a "point cube" for the given canonical vars.
///
/// A point cube has equality constraints that transitively ground each canonical
/// variable to a constant. Uses union-find to track equivalence classes.
///
/// Key insight: `x = y` alone does NOT make either grounded. Only `x = 5` grounds x.
/// But `x = y` AND `y = 5` grounds both x and y through transitivity.
pub(in crate::pdr) fn is_point_cube_for_vars(cube: &ChcExpr, canonical_vars: &[ChcVar]) -> bool {
    let mut uf = PointCubeUnionFind::new();
    collect_equalities_for_point_check(cube, &mut uf);

    // All canonical vars must be in a grounded equivalence class
    canonical_vars.iter().all(|v| uf.is_grounded(&v.name))
}
