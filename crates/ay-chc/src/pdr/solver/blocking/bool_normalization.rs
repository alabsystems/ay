// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bool-Int normalization for interpolation and Farkas conflict extraction.
//!
//! Free functions for converting boolean constraints to integer form and back,
//! used by the blocking algorithm's interpolation pipeline (#5877).

use crate::expr::maybe_grow_expr_stack;
use crate::smt::types::FarkasConflict;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::sync::Arc;

/// Extract Farkas conflicts from an SmtResult, consuming the result (#6484).
///
/// Returns the contained `FarkasConflict` data as a `Vec<FarkasConflict>`:
/// - `UnsatWithFarkas(c)` → `vec![c]`
/// - `UnsatWithCore(core)` → `core.farkas_conflicts`
/// - `Unsat` / other → empty vec
pub(super) fn extract_farkas_from_result(result: SmtResult) -> Vec<FarkasConflict> {
    match result {
        SmtResult::UnsatWithFarkas(conflict) => vec![conflict],
        SmtResult::UnsatWithCore(core) => core.farkas_conflicts,
        _ => Vec::new(),
    }
}

/// #5877: Normalize boolean constraints to 0/1 integer form for interpolation.
///
/// Mixed boolean-integer CHC problems (e.g., BvToInt-converted BV benchmarks) have
/// boolean predicate arguments. The Farkas/FM interpolation engine only handles LIA
/// (linear integer arithmetic) and silently drops boolean constraints. This causes
/// all interpolation strategies to fail when the bad state is purely boolean.
///
/// This normalization converts boolean constraints to equivalent integer constraints:
/// - `(= x true)` → `(>= x_int 1)` where `x_int` has the same name but Int sort
/// - `(= x false)` → `(<= x_int 0)`
/// - `(not x)` where x : Bool → `(<= x_int 0)`
/// - Bare `x` where x : Bool → `(>= x_int 1)`
///
/// Returns the normalized constraints and a set of variable names that were Bool.
pub(super) fn normalize_bool_to_int(constraints: &[ChcExpr]) -> (Vec<ChcExpr>, FxHashSet<String>) {
    let mut bool_var_names: FxHashSet<String> = FxHashSet::default();
    let normalized: Vec<ChcExpr> = constraints
        .iter()
        .map(|c| normalize_bool_expr(c, &mut bool_var_names))
        .collect();
    (normalized, bool_var_names)
}

/// Normalize a single boolean expression to integer form.
fn normalize_bool_expr(expr: &ChcExpr, bool_vars: &mut FxHashSet<String>) -> ChcExpr {
    maybe_grow_expr_stack(|| normalize_bool_expr_inner(expr, bool_vars))
}

fn normalize_bool_expr_inner(expr: &ChcExpr, bool_vars: &mut FxHashSet<String>) -> ChcExpr {
    match expr {
        // (= x true) or (= true x) where x : Bool → (>= x_int 1)
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            if let (ChcExpr::Var(v), ChcExpr::Bool(true)) | (ChcExpr::Bool(true), ChcExpr::Var(v)) =
                (args[0].as_ref(), args[1].as_ref())
            {
                if matches!(v.sort, ChcSort::Bool) {
                    bool_vars.insert(v.name.clone());
                    let int_var = ChcExpr::var(ChcVar::new(v.name.clone(), ChcSort::Int));
                    return ChcExpr::ge(int_var, ChcExpr::Int(1));
                }
            }
            // (= x false) or (= false x) where x : Bool → (<= x_int 0)
            if let (ChcExpr::Var(v), ChcExpr::Bool(false))
            | (ChcExpr::Bool(false), ChcExpr::Var(v)) = (args[0].as_ref(), args[1].as_ref())
            {
                if matches!(v.sort, ChcSort::Bool) {
                    bool_vars.insert(v.name.clone());
                    let int_var = ChcExpr::var(ChcVar::new(v.name.clone(), ChcSort::Int));
                    return ChcExpr::le(int_var, ChcExpr::Int(0));
                }
            }
            // (= x y) where both Bool → (= x_int y_int)
            if let (ChcExpr::Var(v1), ChcExpr::Var(v2)) = (args[0].as_ref(), args[1].as_ref()) {
                if matches!(v1.sort, ChcSort::Bool) && matches!(v2.sort, ChcSort::Bool) {
                    bool_vars.insert(v1.name.clone());
                    bool_vars.insert(v2.name.clone());
                    let iv1 = ChcExpr::var(ChcVar::new(v1.name.clone(), ChcSort::Int));
                    let iv2 = ChcExpr::var(ChcVar::new(v2.name.clone(), ChcSort::Int));
                    return ChcExpr::eq(iv1, iv2);
                }
            }
            // Non-boolean equality — recurse into sub-expressions
            ChcExpr::Op(
                ChcOp::Eq,
                args.iter()
                    .map(|a| Arc::new(normalize_bool_expr(a, bool_vars)))
                    .collect(),
            )
        }
        // (not x) where x : Bool → (<= x_int 0)
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            if let ChcExpr::Var(v) = args[0].as_ref() {
                if matches!(v.sort, ChcSort::Bool) {
                    bool_vars.insert(v.name.clone());
                    let int_var = ChcExpr::var(ChcVar::new(v.name.clone(), ChcSort::Int));
                    return ChcExpr::le(int_var, ChcExpr::Int(0));
                }
            }
            // (not (= x true)) → (<= x_int 0), (not (= x false)) → (>= x_int 1)
            if let ChcExpr::Op(ChcOp::Eq, inner_args) = args[0].as_ref() {
                if inner_args.len() == 2 {
                    if let (ChcExpr::Var(v), ChcExpr::Bool(true))
                    | (ChcExpr::Bool(true), ChcExpr::Var(v)) =
                        (inner_args[0].as_ref(), inner_args[1].as_ref())
                    {
                        if matches!(v.sort, ChcSort::Bool) {
                            bool_vars.insert(v.name.clone());
                            let int_var = ChcExpr::var(ChcVar::new(v.name.clone(), ChcSort::Int));
                            return ChcExpr::le(int_var, ChcExpr::Int(0));
                        }
                    }
                    if let (ChcExpr::Var(v), ChcExpr::Bool(false))
                    | (ChcExpr::Bool(false), ChcExpr::Var(v)) =
                        (inner_args[0].as_ref(), inner_args[1].as_ref())
                    {
                        if matches!(v.sort, ChcSort::Bool) {
                            bool_vars.insert(v.name.clone());
                            let int_var = ChcExpr::var(ChcVar::new(v.name.clone(), ChcSort::Int));
                            return ChcExpr::ge(int_var, ChcExpr::Int(1));
                        }
                    }
                }
            }
            // Recurse
            ChcExpr::Op(
                ChcOp::Not,
                args.iter()
                    .map(|a| Arc::new(normalize_bool_expr(a, bool_vars)))
                    .collect(),
            )
        }
        // Bare Bool variable → (>= x_int 1)
        ChcExpr::Var(v) if matches!(v.sort, ChcSort::Bool) => {
            bool_vars.insert(v.name.clone());
            ChcExpr::ge(
                ChcExpr::var(ChcVar::new(v.name.clone(), ChcSort::Int)),
                ChcExpr::Int(1),
            )
        }
        // And/Or — recurse
        ChcExpr::Op(op @ (ChcOp::And | ChcOp::Or | ChcOp::Implies), args) => ChcExpr::Op(
            *op,
            args.iter()
                .map(|a| Arc::new(normalize_bool_expr(a, bool_vars)))
                .collect(),
        ),
        // Everything else (Int comparisons, arithmetic, etc.) — pass through
        _ => expr.clone(),
    }
}

/// #5877: Convert an integer-encoded interpolant back to boolean form.
///
/// After interpolation produces an expression over Int-sorted variables that were
/// originally Bool, this converts patterns like `(>= x 1)` → `x` (Bool) and
/// `(<= x 0)` → `(not x)`.
pub(super) fn denormalize_int_to_bool(expr: &ChcExpr, bool_vars: &FxHashSet<String>) -> ChcExpr {
    if bool_vars.is_empty() {
        return expr.clone();
    }
    maybe_grow_expr_stack(|| denormalize_int_to_bool_inner(expr, bool_vars))
}

fn denormalize_int_to_bool_inner(expr: &ChcExpr, bool_vars: &FxHashSet<String>) -> ChcExpr {
    match expr {
        // (>= x 1) where x was Bool → x (Bool)
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            if let (ChcExpr::Var(v), ChcExpr::Int(1)) = (args[0].as_ref(), args[1].as_ref()) {
                if bool_vars.contains(&v.name) {
                    return ChcExpr::var(ChcVar::new(v.name.clone(), ChcSort::Bool));
                }
            }
            expr.clone()
        }
        // (<= x 0) where x was Bool → (not x) (Bool)
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            if let (ChcExpr::Var(v), ChcExpr::Int(0)) = (args[0].as_ref(), args[1].as_ref()) {
                if bool_vars.contains(&v.name) {
                    return ChcExpr::not(ChcExpr::var(ChcVar::new(v.name.clone(), ChcSort::Bool)));
                }
            }
            expr.clone()
        }
        // (= x y) where both were Bool → (= x y) with Bool sort
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            if let (ChcExpr::Var(v1), ChcExpr::Var(v2)) = (args[0].as_ref(), args[1].as_ref()) {
                if bool_vars.contains(&v1.name) && bool_vars.contains(&v2.name) {
                    return ChcExpr::eq(
                        ChcExpr::var(ChcVar::new(v1.name.clone(), ChcSort::Bool)),
                        ChcExpr::var(ChcVar::new(v2.name.clone(), ChcSort::Bool)),
                    );
                }
            }
            expr.clone()
        }
        // Recurse into And/Or/Not/Implies
        ChcExpr::Op(op @ (ChcOp::And | ChcOp::Or | ChcOp::Not | ChcOp::Implies), args) => {
            ChcExpr::Op(
                *op,
                args.iter()
                    .map(|a| Arc::new(denormalize_int_to_bool(a, bool_vars)))
                    .collect(),
            )
        }
        _ => expr.clone(),
    }
}
