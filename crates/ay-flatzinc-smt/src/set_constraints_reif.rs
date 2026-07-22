// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Reified set comparison constraints for FlatZinc-to-SMT-LIB translation.
// Pattern: `constraint_reif(S1, S2, r)` → r <=> condition(S1, S2)
// Encoded as two implications: `r => condition` and `condition => r`.
// Split from set_constraints.rs to keep files under 500 lines.

use ay_flatzinc_parser::ast::Expr;

use crate::builtins::check_args;
use crate::error::TranslateError;
use crate::set_constraints::{
    resolve_set_domain, set_lex_condition, set_membership_term, SetLexOrder,
};
use crate::translate::Context;

fn conjunction(terms: &[String]) -> String {
    match terms {
        [] => "true".to_string(),
        [term] => term.clone(),
        _ => format!("(and {})", terms.join(" ")),
    }
}

fn disjunction(terms: &[String]) -> String {
    match terms {
        [] => "false".to_string(),
        [term] => term.clone(),
        _ => format!("(or {})", terms.join(" ")),
    }
}

/// `set_eq_reif(S1, S2, r)` → r <=> (for all i: S1_bit_i = S2_bit_i)
pub(crate) fn set_eq_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_eq_reif", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_eq_reif")?;
    let eqs: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_eq_reif")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_eq_reif")?;
            Ok(format!("(= {b1} {b2})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    let cond = conjunction(&eqs);

    ctx.emit_fmt(format_args!("(assert (=> {r} {cond}))"));
    ctx.emit_fmt(format_args!("(assert (=> {cond} {r}))"));
    Ok(())
}

/// `set_ne_reif(S1, S2, r)` → r <=> (exists i: S1_bit_i ≠ S2_bit_i)
pub(crate) fn set_ne_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_ne_reif", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_ne_reif")?;
    let diffs: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_ne_reif")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_ne_reif")?;
            Ok(format!("(xor {b1} {b2})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    let cond = disjunction(&diffs);

    ctx.emit_fmt(format_args!("(assert (=> {r} {cond}))"));
    ctx.emit_fmt(format_args!("(assert (=> {cond} {r}))"));
    Ok(())
}

/// `set_subset_reif(S1, S2, r)` → r <=> (for all i: S1_bit_i => S2_bit_i)
pub(crate) fn set_subset_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_subset_reif", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_subset_reif")?;
    let impls: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_subset_reif")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_subset_reif")?;
            Ok(format!("(=> {b1} {b2})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    let cond = conjunction(&impls);

    ctx.emit_fmt(format_args!("(assert (=> {r} {cond}))"));
    ctx.emit_fmt(format_args!("(assert (=> {cond} {r}))"));
    Ok(())
}

/// `set_le_reif(S1, S2, r)` → r iff the sorted element list of S1 is
/// lexicographically less than or equal to that of S2.
pub(crate) fn set_le_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_le_reif", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;
    let condition = set_lex_condition(ctx, &s1, &s2, SetLexOrder::LessEqual, "set_le_reif")?;
    ctx.emit_fmt(format_args!("(assert (= {r} {condition}))"));
    Ok(())
}

/// `set_lt_reif(S1, S2, r)` → r iff the sorted element list of S1 is
/// lexicographically less than that of S2.
pub(crate) fn set_lt_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_lt_reif", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;
    let condition = set_lex_condition(ctx, &s1, &s2, SetLexOrder::Less, "set_lt_reif")?;
    ctx.emit_fmt(format_args!("(assert (= {r} {condition}))"));
    Ok(())
}

/// `set_superset_reif(S1, S2, r)` → r <=> S1 ⊇ S2.
pub(crate) fn set_superset_reif(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_superset_reif", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let r = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_superset_reif")?;
    let impls: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_superset_reif")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_superset_reif")?;
            Ok(format!("(=> {b2} {b1})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    let cond = conjunction(&impls);

    ctx.emit_fmt(format_args!("(assert (=> {r} {cond}))"));
    ctx.emit_fmt(format_args!("(assert (=> {cond} {r}))"));
    Ok(())
}
