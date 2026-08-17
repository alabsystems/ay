// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Built-in FlatZinc constraint translations to SMT-LIB2

mod boolean;

use ay_flatzinc_parser::ast::{ConstraintItem, Expr};

use crate::error::TranslateError;
use crate::translate::{Context, SmtInt};

/// Translate a built-in FlatZinc constraint. Returns Ok(true) if handled.
pub(crate) fn translate_builtin(
    ctx: &mut Context,
    c: &ConstraintItem,
) -> Result<bool, TranslateError> {
    let args = &c.args;
    let handled = match c.id.as_str() {
        // Integer comparison
        "int_eq" => {
            binary_assert(ctx, args, "=")?;
            true
        }
        "int_ne" => {
            binary_assert_neg(ctx, args, "=")?;
            true
        }
        "int_lt" => {
            binary_assert(ctx, args, "<")?;
            true
        }
        "int_le" => {
            binary_assert(ctx, args, "<=")?;
            true
        }
        "int_gt" => {
            binary_assert(ctx, args, ">")?;
            true
        }
        "int_ge" => {
            binary_assert(ctx, args, ">=")?;
            true
        }
        // Boolean comparison and logic
        "bool_eq" => {
            binary_assert(ctx, args, "=")?;
            true
        }
        "bool_not" => {
            boolean::bool_not(ctx, args)?;
            true
        }
        "bool_and" => {
            boolean::ternary_bool_func(ctx, args, "and")?;
            true
        }
        "bool_or" => {
            boolean::ternary_bool_func(ctx, args, "or")?;
            true
        }
        "bool_xor" => {
            boolean::ternary_bool_func(ctx, args, "xor")?;
            true
        }
        "bool_clause" => {
            boolean::bool_clause(ctx, args)?;
            true
        }
        // Array boolean logic
        "array_bool_and" => {
            boolean::array_bool_and(ctx, args)?;
            true
        }
        "array_bool_or" => {
            boolean::array_bool_or(ctx, args)?;
            true
        }
        "array_bool_xor" => {
            boolean::array_bool_xor(ctx, args)?;
            true
        }
        // Integer arithmetic
        "int_plus" => {
            crate::builtins_arithmetic::ternary_func(ctx, args, "+")?;
            true
        }
        "int_minus" => {
            crate::builtins_arithmetic::ternary_func(ctx, args, "-")?;
            true
        }
        "int_times" => {
            crate::builtins_arithmetic::int_times(ctx, args)?;
            true
        }
        "int_div" => {
            crate::builtins_arithmetic::int_div(ctx, args)?;
            true
        }
        "int_mod" => {
            crate::builtins_arithmetic::int_mod(ctx, args)?;
            true
        }
        "int_negate" => {
            int_negate(ctx, args)?;
            true
        }
        "int_abs" => {
            int_abs(ctx, args)?;
            true
        }
        "int_min" => {
            int_minmax(ctx, args, "<=")?;
            true
        }
        "int_max" => {
            int_minmax(ctx, args, ">=")?;
            true
        }
        "int_pow" => {
            crate::builtins_extra::int_pow(ctx, args)?;
            true
        }
        // Linear constraints
        "int_lin_eq" => {
            crate::builtins_extra::int_lin(ctx, args, "=")?;
            true
        }
        "int_lin_le" => {
            crate::builtins_extra::int_lin(ctx, args, "<=")?;
            true
        }
        "int_lin_ne" => {
            crate::builtins_extra::int_lin_ne(ctx, args)?;
            true
        }
        // Boolean linear
        "bool_lin_eq" => {
            crate::builtins_extra::bool_lin(ctx, args, "=")?;
            true
        }
        "bool_lin_le" => {
            crate::builtins_extra::bool_lin(ctx, args, "<=")?;
            true
        }
        // Array element access
        "array_int_element"
        | "array_var_int_element"
        | "array_bool_element"
        | "array_var_bool_element" => {
            array_element(ctx, c.id.as_str(), args)?;
            true
        }
        // Type conversion
        "bool2int" => {
            bool2int(ctx, args)?;
            true
        }
        // Set membership
        "set_in" => {
            set_in(ctx, args)?;
            true
        }
        // Reified variants (in builtins_extra.rs)
        "int_eq_reif" => {
            crate::builtins_extra::reified_binary(ctx, args, "=")?;
            true
        }
        "int_ne_reif" => {
            crate::builtins_extra::reified_binary_neg(ctx, args, "=")?;
            true
        }
        "int_lt_reif" => {
            crate::builtins_extra::reified_binary(ctx, args, "<")?;
            true
        }
        "int_le_reif" => {
            crate::builtins_extra::reified_binary(ctx, args, "<=")?;
            true
        }
        "int_gt_reif" => {
            crate::builtins_extra::reified_binary(ctx, args, ">")?;
            true
        }
        "int_ge_reif" => {
            crate::builtins_extra::reified_binary(ctx, args, ">=")?;
            true
        }
        "bool_eq_reif" => {
            crate::builtins_extra::reified_binary(ctx, args, "=")?;
            true
        }
        "int_lin_eq_reif" => {
            crate::builtins_extra::int_lin_reif(ctx, args, "=")?;
            true
        }
        "int_lin_le_reif" => {
            crate::builtins_extra::int_lin_reif(ctx, args, "<=")?;
            true
        }
        "int_lin_ne_reif" => {
            crate::builtins_extra::int_lin_ne_reif(ctx, args)?;
            true
        }
        "set_in_reif" => {
            crate::builtins_extra::set_in_reif(ctx, args)?;
            true
        }
        // Set variable constraints (boolean decomposition)
        "set_card" => {
            crate::set_constraints::set_card(ctx, args)?;
            true
        }
        "set_union" => {
            crate::set_constraints::set_union(ctx, args)?;
            true
        }
        "array_set_element" => {
            crate::set_constraints::array_set_element(ctx, args)?;
            true
        }
        "set_intersect" => {
            crate::set_constraints::set_intersect(ctx, args)?;
            true
        }
        "set_diff" => {
            crate::set_constraints::set_diff(ctx, args)?;
            true
        }
        "set_symdiff" => {
            crate::set_constraints::set_symdiff(ctx, args)?;
            true
        }
        "set_subset" => {
            crate::set_constraints::set_subset(ctx, args)?;
            true
        }
        "set_superset" => {
            crate::set_constraints::set_superset(ctx, args)?;
            true
        }
        "set_eq" => {
            crate::set_constraints::set_eq(ctx, args)?;
            true
        }
        "set_ne" => {
            crate::set_constraints::set_ne(ctx, args)?;
            true
        }
        "set_le" => {
            crate::set_constraints::set_le(ctx, args)?;
            true
        }
        "set_lt" => {
            crate::set_constraints::set_lt(ctx, args)?;
            true
        }
        // Reified set comparison constraints
        "set_eq_reif" => {
            crate::set_constraints_reif::set_eq_reif(ctx, args)?;
            true
        }
        "set_ne_reif" => {
            crate::set_constraints_reif::set_ne_reif(ctx, args)?;
            true
        }
        "set_subset_reif" => {
            crate::set_constraints_reif::set_subset_reif(ctx, args)?;
            true
        }
        "set_superset_reif" => {
            crate::set_constraints_reif::set_superset_reif(ctx, args)?;
            true
        }
        "set_le_reif" => {
            crate::set_constraints_reif::set_le_reif(ctx, args)?;
            true
        }
        "set_lt_reif" => {
            crate::set_constraints_reif::set_lt_reif(ctx, args)?;
            true
        }
        _ => false,
    };
    Ok(handled)
}

pub(crate) fn check_args(name: &str, args: &[Expr], expected: usize) -> Result<(), TranslateError> {
    if args.len() != expected {
        return Err(TranslateError::WrongArgCount {
            name: name.into(),
            expected,
            got: args.len(),
        });
    }
    Ok(())
}

/// `constraint op(a, b)` → `(assert (op a b))`
fn binary_assert(ctx: &mut Context, args: &[Expr], op: &str) -> Result<(), TranslateError> {
    check_args(op, args, 2)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    ctx.emit_fmt(format_args!("(assert ({op} {a} {b}))"));
    Ok(())
}

/// `constraint ne(a, b)` → `(assert (not (= a b)))`
fn binary_assert_neg(ctx: &mut Context, args: &[Expr], op: &str) -> Result<(), TranslateError> {
    check_args(op, args, 2)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    ctx.emit_fmt(format_args!("(assert (not ({op} {a} {b})))"));
    Ok(())
}

/// `int_negate(a, b)` → `(assert (= b (- a)))`
fn int_negate(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("int_negate", args, 2)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    ctx.emit_fmt(format_args!("(assert (= {b} (- {a})))"));
    Ok(())
}

/// `int_abs(a, b)` → `(assert (= b (ite (>= a 0) a (- a))))`
fn int_abs(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("int_abs", args, 2)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    ctx.emit_fmt(format_args!(
        "(assert (= {b} (ite (>= {a} 0) {a} (- {a}))))"
    ));
    Ok(())
}

/// `int_min(a, b, c)` or `int_max(a, b, c)` using ite.
fn int_minmax(ctx: &mut Context, args: &[Expr], cmp: &str) -> Result<(), TranslateError> {
    check_args("int_min/max", args, 3)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    let c = ctx.expr_to_smt(&args[2])?;
    ctx.emit_fmt(format_args!(
        "(assert (= {c} (ite ({cmp} {a} {b}) {a} {b})))"
    ));
    Ok(())
}

/// `array_*_element(idx, arr, val)` → ite chain asserting val = arr[idx]
fn array_element(ctx: &mut Context, name: &str, args: &[Expr]) -> Result<(), TranslateError> {
    check_args(name, args, 3)?;
    let idx = ctx.expr_to_smt(&args[0])?;
    let (array_lo, array_hi, arr) = ctx.expr_to_smt_indexed_array(&args[1])?;
    let val = ctx.expr_to_smt(&args[2])?;
    if arr.is_empty() {
        return Err(TranslateError::UnsupportedType(format!(
            "{name}: empty array"
        )));
    }
    // Build an ITE chain using the source expression's declared index range.
    let n = arr.len();
    ctx.emit_fmt(format_args!(
        "(assert (and (>= {idx} {}) (<= {idx} {})))",
        SmtInt(array_lo),
        SmtInt(array_hi)
    ));
    let mut ite = arr[n - 1].clone();
    for i in (0..n - 1).rev() {
        let offset = i64::try_from(i).map_err(|_| {
            TranslateError::UnsupportedType(format!("{name}: array index is too large"))
        })?;
        let idx_val = array_lo.checked_add(offset).ok_or_else(|| {
            TranslateError::UnsupportedType(format!("{name}: array index overflows i64"))
        })?;
        ite = format!("(ite (= {idx} {}) {} {ite})", SmtInt(idx_val), arr[i]);
    }
    ctx.emit_fmt(format_args!("(assert (= {val} {ite}))"));
    Ok(())
}

/// `bool2int(b, i)` → `(assert (= i (ite b 1 0)))`
fn bool2int(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("bool2int", args, 2)?;
    let b = ctx.expr_to_smt(&args[0])?;
    let i = ctx.expr_to_smt(&args[1])?;
    ctx.emit_fmt(format_args!("(assert (= {i} (ite {b} 1 0)))"));
    Ok(())
}

/// `set_in(x, S)` → domain constraint
fn set_in(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_in", args, 2)?;
    // Check if second arg is a set variable (boolean decomposition)
    if let Expr::Ident(name) = &args[1] {
        if ctx.set_vars.contains_key(name) {
            return crate::set_constraints::set_in_var(ctx, args);
        }
    }
    let x = ctx.expr_to_smt(&args[0])?;
    let values = ctx.resolve_set(&args[1])?;
    if values.is_empty() {
        ctx.emit("(assert false)");
    } else if values.len() == 1 {
        ctx.emit_fmt(format_args!("(assert (= {x} {}))", SmtInt(values[0])));
    } else {
        let disjuncts: Vec<String> = values
            .iter()
            .map(|v| format!("(= {x} {})", SmtInt(*v)))
            .collect();
        ctx.emit_fmt(format_args!("(assert (or {}))", disjuncts.join(" ")));
    }
    Ok(())
}
