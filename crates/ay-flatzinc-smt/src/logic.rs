// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// SMT-LIB logic classification for translated FlatZinc models.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet};
use ay_flatzinc_parser::ast::{Expr, FznModel, FznType};

use crate::builtins_arithmetic::LINEARIZE_DOMAIN_LIMIT;

/// Check if an expression is a constant (integer literal or parameter reference).
///
/// Used by `detect_logic` to distinguish truly nonlinear constraints
/// (variable * variable) from linear ones (constant * variable).
fn is_constant_expr(param_names: &DetHashSet<&str>, expr: &Expr) -> bool {
    match expr {
        Expr::Bool(_) | Expr::Int(_) | Expr::Float(_) => true,
        Expr::Ident(name) => param_names.contains(name.as_str()),
        _ => false,
    }
}

/// Detect the appropriate SMT-LIB logic for the model.
///
/// Set variables use boolean decomposition (no bitvectors), so they are
/// compatible with QF_LIA. Returns `QF_NIA` only if genuinely nonlinear
/// operations are detected (both operands are variables), `QF_LIA` otherwise.
///
/// `int_times(a, b, r)` where one of a/b is a constant is just linear
/// multiplication (e.g., `r = 3 * x`). Only `variable * variable` requires
/// QF_NIA. Similarly, `int_mod(constant, constant, r)` is a constant
/// computation — not nonlinear.
pub(super) fn detect_logic(model: &FznModel) -> &'static str {
    // Build a set of parameter names for constant detection.
    let param_names: DetHashSet<&str> = model.parameters.iter().map(|p| p.id.as_str()).collect();

    // Build a map of variable domain sizes for linearization detection.
    let var_domain_size: HashMap<&str, i64> = model
        .variables
        .iter()
        .filter_map(|v| {
            let size = match &v.ty {
                FznType::Bool => 2,
                FznType::IntRange(lo, hi) => {
                    let size = i128::from(*hi) - i128::from(*lo) + 1;
                    if size <= 0 {
                        0
                    } else {
                        i64::try_from(size).unwrap_or(i64::MAX)
                    }
                }
                FznType::IntSet(vals) => i64::try_from(vals.len()).unwrap_or(i64::MAX),
                _ => return None,
            };
            Some((v.id.as_str(), size))
        })
        .collect();

    let int_param_values: HashMap<&str, i64> = model
        .parameters
        .iter()
        .filter_map(|parameter| match &parameter.value {
            Expr::Int(value) => Some((parameter.id.as_str(), *value)),
            _ => None,
        })
        .collect();

    let has_nonlinear = model.constraints.iter().any(|c| match c.id.as_str() {
        "int_times" => {
            // Nonlinear only if both operands are variables AND neither has a
            // small enough domain for ITE-chain linearization.
            if c.args.len() < 2 {
                return false;
            }
            if is_constant_expr(&param_names, &c.args[0])
                || is_constant_expr(&param_names, &c.args[1])
            {
                return false;
            }
            // If either operand is a variable with a small domain, it will be
            // linearized by the builtins handler — not truly nonlinear.
            let a_small = expr_has_small_domain(&c.args[0], &var_domain_size);
            let b_small = expr_has_small_domain(&c.args[1], &var_domain_size);
            !a_small && !b_small
        }
        "int_div" | "int_mod" => c.args.len() >= 2 && !is_constant_expr(&param_names, &c.args[1]),
        "int_pow" => {
            if c.args.len() < 2 || is_constant_expr(&param_names, &c.args[0]) {
                return false;
            }
            match constant_int_value(&c.args[1], &int_param_values) {
                Some(exponent) => exponent >= 2,
                // An unresolved parameter is still conservatively
                // nonlinear; a variable exponent may select a power >= 2.
                None => true,
            }
        }
        _ => false,
    });
    if has_nonlinear {
        "QF_NIA"
    } else {
        "QF_LIA"
    }
}

fn constant_int_value(expr: &Expr, parameters: &HashMap<&str, i64>) -> Option<i64> {
    match expr {
        Expr::Int(value) => Some(*value),
        Expr::Ident(name) => parameters.get(name.as_str()).copied(),
        _ => None,
    }
}

/// Check if a FlatZinc expression refers to a variable with a small enough domain
/// for linearization.
fn expr_has_small_domain(expr: &Expr, var_domain_size: &HashMap<&str, i64>) -> bool {
    match expr {
        Expr::Ident(name) => var_domain_size
            .get(name.as_str())
            .is_some_and(|&size| size > 0 && size <= LINEARIZE_DOMAIN_LIMIT),
        _ => false,
    }
}
