// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Built-in FlatZinc constraint translations to SMT-LIB2

use ay_flatzinc_parser::ast::{ConstraintItem, Expr};

use crate::error::TranslateError;
use crate::translate::{smt_int, Context, SmtInt, VarDomain};

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
            bool_not(ctx, args)?;
            true
        }
        "bool_and" => {
            ternary_bool_func(ctx, args, "and")?;
            true
        }
        "bool_or" => {
            ternary_bool_func(ctx, args, "or")?;
            true
        }
        "bool_xor" => {
            ternary_bool_func(ctx, args, "xor")?;
            true
        }
        "bool_clause" => {
            bool_clause(ctx, args)?;
            true
        }
        // Array boolean logic
        "array_bool_and" => {
            array_bool_and(ctx, args)?;
            true
        }
        "array_bool_or" => {
            array_bool_or(ctx, args)?;
            true
        }
        "array_bool_xor" => {
            array_bool_xor(ctx, args)?;
            true
        }
        // Integer arithmetic
        "int_plus" => {
            ternary_func(ctx, args, "+")?;
            true
        }
        "int_minus" => {
            ternary_func(ctx, args, "-")?;
            true
        }
        "int_times" => {
            int_times(ctx, args)?;
            true
        }
        "int_div" => {
            ternary_func(ctx, args, "div")?;
            true
        }
        "int_mod" => {
            ternary_func(ctx, args, "mod")?;
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

/// `constraint op(a, b, r)` → `(assert (= r (op a b)))` for Int-typed results
fn ternary_func(ctx: &mut Context, args: &[Expr], op: &str) -> Result<(), TranslateError> {
    check_args(op, args, 3)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;
    ctx.emit_fmt(format_args!("(assert (= {r} ({op} {a} {b})))"));
    Ok(())
}

/// Maximum domain size for linearizing `int_times(a, b, r)`.
/// When one operand has at most this many values, the product is encoded as
/// an ITE chain over its domain, avoiding QF_NIA.
const LINEARIZE_DOMAIN_LIMIT: i64 = 32;

/// `int_times(a, b, r)` — linearize when one operand has a small bounded domain.
///
/// If operand `a` has domain `{v1, v2, ..., vk}` with k ≤ LINEARIZE_DOMAIN_LIMIT,
/// emit: `r = ite(a = v1, v1*b, ite(a = v2, v2*b, ... vk*b ...))`.
/// This keeps the logic in QF_LIA instead of QF_NIA.
fn int_times(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("int_times", args, 3)?;

    // Try to find a small-domain operand for linearization.
    let small_domain = expr_small_domain(ctx, &args[0]);
    let (case_values, case_idx) = match &small_domain {
        Some(vals) if vals.len() <= LINEARIZE_DOMAIN_LIMIT as usize => (vals.clone(), 0usize),
        _ => {
            let other = expr_small_domain(ctx, &args[1]);
            match other {
                Some(vals) if vals.len() <= LINEARIZE_DOMAIN_LIMIT as usize => (vals, 1usize),
                _ => {
                    // Both operands have large/unknown domains — fall back to nonlinear `*`.
                    return ternary_func(ctx, args, "*");
                }
            }
        }
    };

    let other_idx = 1 - case_idx;
    let case_var = ctx.expr_to_smt(&args[case_idx])?;
    let other_var = ctx.expr_to_smt(&args[other_idx])?;
    let r = ctx.expr_to_smt(&args[2])?;

    // Build ITE chain: ite(case_var = v1, v1*other, ite(case_var = v2, v2*other, ...))
    if case_values.is_empty() {
        ctx.emit("(assert false)");
        return Ok(());
    }

    let ite_expr = build_linear_ite(&case_var, &other_var, &case_values);
    ctx.emit_fmt(format_args!("(assert (= {r} {ite_expr}))"));
    Ok(())
}

/// Build an ITE chain: `ite(x=v1, v1*y, ite(x=v2, v2*y, ... vk*y))`.
fn build_linear_ite(case_var: &str, other_var: &str, values: &[i64]) -> String {
    debug_assert!(!values.is_empty());
    if values.len() == 1 {
        return linear_product_term(values[0], other_var);
    }

    let mut result = linear_product_term(
        *values.last().expect("invariant: non-empty values"),
        other_var,
    );
    for &v in values[..values.len() - 1].iter().rev() {
        let prod = linear_product_term(v, other_var);
        result = format!(
            "(ite (= {case_var} {val}) {prod} {result})",
            val = smt_int(v)
        );
    }
    result
}

/// Generate a linear product term `v * other` as an SMT expression.
fn linear_product_term(v: i64, other_var: &str) -> String {
    match v {
        0 => "0".to_string(),
        1 => other_var.to_string(),
        -1 => format!("(- {other_var})"),
        _ => format!("(* {} {other_var})", smt_int(v)),
    }
}

/// Get the domain values for an expression if it refers to a variable with a small
/// bounded domain. Returns None for non-variables or large/unbounded domains.
fn expr_small_domain(ctx: &Context, expr: &Expr) -> Option<Vec<i64>> {
    let name = match expr {
        Expr::Ident(name) => name.as_str(),
        _ => return None,
    };
    match ctx.var_domains.get(name)? {
        VarDomain::Bool => Some(vec![0, 1]),
        VarDomain::IntRange(lo, hi) => {
            let size = hi.checked_sub(*lo)?.checked_add(1)?;
            if size > 0 && size <= LINEARIZE_DOMAIN_LIMIT {
                Some((*lo..=*hi).collect())
            } else {
                None
            }
        }
        VarDomain::IntSet(vals) => {
            if vals.len() <= LINEARIZE_DOMAIN_LIMIT as usize {
                Some(vals.clone())
            } else {
                None
            }
        }
        VarDomain::IntUnbounded => None,
    }
}

/// `bool_op(a, b, r)` → iff decomposition for Bool-typed results
fn ternary_bool_func(ctx: &mut Context, args: &[Expr], op: &str) -> Result<(), TranslateError> {
    check_args(op, args, 3)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;
    ctx.emit_fmt(format_args!("(assert (=> {r} ({op} {a} {b})))"));
    ctx.emit_fmt(format_args!("(assert (=> ({op} {a} {b}) {r}))"));
    Ok(())
}

/// `bool_not(a, b)` → iff decomposition: `b => (not a)` ∧ `(not a) => b`
fn bool_not(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("bool_not", args, 2)?;
    let a = ctx.expr_to_smt(&args[0])?;
    let b = ctx.expr_to_smt(&args[1])?;
    ctx.emit_fmt(format_args!("(assert (=> {b} (not {a})))"));
    ctx.emit_fmt(format_args!("(assert (=> (not {a}) {b}))"));
    Ok(())
}

/// `bool_clause(pos, neg)` → `(assert (or pos... (not neg)...))`
fn bool_clause(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("bool_clause", args, 2)?;
    let pos = ctx.expr_to_smt_array(&args[0])?;
    let neg = ctx.expr_to_smt_array(&args[1])?;
    let mut terms = pos;
    for n in &neg {
        terms.push(format!("(not {n})"));
    }
    if terms.is_empty() {
        ctx.emit("(assert false)");
    } else if terms.len() == 1 {
        ctx.emit_fmt(format_args!("(assert {})", terms[0]));
    } else {
        ctx.emit_fmt(format_args!("(assert (or {}))", terms.join(" ")));
    }
    Ok(())
}

/// `array_bool_and(bs, r)` → iff decomposition: `r => (and bs)` ∧ `(and bs) => r`
///
/// r is true iff all elements of bs are true.
fn array_bool_and(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("array_bool_and", args, 2)?;
    let bs = ctx.expr_to_smt_array(&args[0])?;
    let r = ctx.expr_to_smt(&args[1])?;
    if bs.is_empty() {
        // Conjunction of empty set is vacuously true
        ctx.emit_fmt(format_args!("(assert {r})"));
    } else if bs.len() == 1 {
        ctx.emit_fmt(format_args!("(assert (=> {r} {}))", bs[0]));
        ctx.emit_fmt(format_args!("(assert (=> {} {r}))", bs[0]));
    } else {
        let conjunction = format!("(and {})", bs.join(" "));
        ctx.emit_fmt(format_args!("(assert (=> {r} {conjunction}))"));
        ctx.emit_fmt(format_args!("(assert (=> {conjunction} {r}))"));
    }
    Ok(())
}

/// `array_bool_or(bs, r)` → iff decomposition: `r => (or bs)` ∧ `(or bs) => r`
///
/// r is true iff at least one element of bs is true.
fn array_bool_or(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("array_bool_or", args, 2)?;
    let bs = ctx.expr_to_smt_array(&args[0])?;
    let r = ctx.expr_to_smt(&args[1])?;
    if bs.is_empty() {
        // Disjunction of empty set is false
        ctx.emit_fmt(format_args!("(assert (not {r}))"));
    } else if bs.len() == 1 {
        ctx.emit_fmt(format_args!("(assert (=> {r} {}))", bs[0]));
        ctx.emit_fmt(format_args!("(assert (=> {} {r}))", bs[0]));
    } else {
        let disjunction = format!("(or {})", bs.join(" "));
        ctx.emit_fmt(format_args!("(assert (=> {r} {disjunction}))"));
        ctx.emit_fmt(format_args!("(assert (=> {disjunction} {r}))"));
    }
    Ok(())
}

/// `array_bool_xor(bs)` → parity constraint (odd number of elements true)
///
/// Uses chained binary xor since SMT-LIB `xor` is binary.
fn array_bool_xor(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("array_bool_xor", args, 1)?;
    let bs = ctx.expr_to_smt_array(&args[0])?;
    if bs.is_empty() {
        // xor of empty set is false → constraint is unsatisfiable
        ctx.emit("(assert false)");
    } else if bs.len() == 1 {
        ctx.emit_fmt(format_args!("(assert {})", bs[0]));
    } else {
        // Chain binary xor: (xor b1 (xor b2 (... bN)))
        let mut expr = bs[bs.len() - 1].clone();
        for i in (0..bs.len() - 1).rev() {
            expr = format!("(xor {} {expr})", bs[i]);
        }
        ctx.emit_fmt(format_args!("(assert {expr})"));
    }
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
