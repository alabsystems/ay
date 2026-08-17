// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `set_constraints` to preserve item DefPaths.

/// Helper: 3-set bitwise operation.  S3_bit_i = op(S1_bit_i, S2_bit_i)
/// `smt_op` is the SMT-LIB operator applied per bit: "and", "or", "xor".
/// `complement_s2` wraps S2 bits in `(not ...)` when true (for set_diff).
fn set_bitwise_op(
    ctx: &mut Context,
    args: &[Expr],
    name: &str,
    smt_op: &str,
    complement_s2: bool,
) -> Result<(), TranslateError> {
    check_args(name, args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let s3 = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain3(ctx, &s1, &s2, &s3, name)?;

    for value in lo..=hi {
        let b1 = set_membership_term(ctx, &s1, value, name)?;
        let b2_raw = set_membership_term(ctx, &s2, value, name)?;
        let b2 = if complement_s2 {
            format!("(not {b2_raw})")
        } else {
            b2_raw
        };
        let b3 = set_membership_term(ctx, &s3, value, name)?;
        ctx.emit_fmt(format_args!("(assert (= {b3} ({smt_op} {b1} {b2})))"));
    }
    Ok(())
}

/// `set_intersect(S1, S2, S3)` → for each bit: S3_bit_i = S1_bit_i and S2_bit_i
pub(crate) fn set_intersect(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    set_bitwise_op(ctx, args, "set_intersect", "and", false)
}

/// `set_diff(S1, S2, S3)` → for each bit: S3_bit_i = S1_bit_i and (not S2_bit_i)
pub(crate) fn set_diff(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    set_bitwise_op(ctx, args, "set_diff", "and", true)
}

/// `set_symdiff(S1, S2, S3)` → for each bit: S3_bit_i = S1_bit_i xor S2_bit_i
pub(crate) fn set_symdiff(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    set_bitwise_op(ctx, args, "set_symdiff", "xor", false)
}

/// Helper: look up set domain from either operand (try both).
pub(crate) fn resolve_set_domain(
    ctx: &Context,
    s1: &str,
    s2: &str,
    name: &str,
) -> Result<(i64, i64), TranslateError> {
    let (lo1, hi1) = lookup_set_domain(ctx, s1, name)?;
    let (lo2, hi2) = lookup_set_domain(ctx, s2, name)?;
    union_set_domains(&[(lo1, hi1), (lo2, hi2)], name)
}

/// `set_subset(S1, S2)` → for each bit: S1_bit_i => S2_bit_i
pub(crate) fn set_subset(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_subset", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_subset")?;

    for value in lo..=hi {
        let b1 = set_membership_term(ctx, &s1, value, "set_subset")?;
        let b2 = set_membership_term(ctx, &s2, value, "set_subset")?;
        ctx.emit_fmt(format_args!("(assert (=> {b1} {b2}))"));
    }
    Ok(())
}

/// `set_superset(S1, S2)` → for each bit: S2_bit_i => S1_bit_i (reverse of subset)
pub(crate) fn set_superset(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_superset", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_superset")?;

    for value in lo..=hi {
        let b1 = set_membership_term(ctx, &s1, value, "set_superset")?;
        let b2 = set_membership_term(ctx, &s2, value, "set_superset")?;
        ctx.emit_fmt(format_args!("(assert (=> {b2} {b1}))"));
    }
    Ok(())
}

/// `set_eq(S1, S2)` → for each bit: S1_bit_i = S2_bit_i
pub(crate) fn set_eq(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_eq", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_eq")?;

    for value in lo..=hi {
        let b1 = set_membership_term(ctx, &s1, value, "set_eq")?;
        let b2 = set_membership_term(ctx, &s2, value, "set_eq")?;
        ctx.emit_fmt(format_args!("(assert (= {b1} {b2}))"));
    }
    Ok(())
}

/// `set_ne(S1, S2)` → at least one bit position differs
pub(crate) fn set_ne(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_ne", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = resolve_set_domain(ctx, &s1, &s2, "set_ne")?;

    let diffs: Vec<String> = (lo..=hi)
        .map(|value| {
            let b1 = set_membership_term(ctx, &s1, value, "set_ne")?;
            let b2 = set_membership_term(ctx, &s2, value, "set_ne")?;
            Ok(format!("(xor {b1} {b2})"))
        })
        .collect::<Result<_, TranslateError>>()?;

    match diffs.as_slice() {
        [] => ctx.emit("(assert false)"),
        [term] => ctx.emit_fmt(format_args!("(assert {term})")),
        _ => ctx.emit_fmt(format_args!("(assert (or {}))", diffs.join(" "))),
    }
    Ok(())
}

#[derive(Clone, Copy)]
pub(crate) enum SetLexOrder {
    Less,
    LessEqual,
}

/// Build a Boolean term for lexicographic comparison of the operands' sorted
/// element lists.
///
/// Characteristic-vector lexicographic order is not the same relation: for
/// example, `{1}` is a proper prefix of `{1, 2}` and therefore compares less,
/// while their characteristic vectors compare in the opposite direction.  The
/// recurrence below tracks whether either remaining suffix is non-empty and
/// whether the already-consumed equal prefix compares in the requested order.
pub(crate) fn set_lex_condition(
    ctx: &mut Context,
    s1: &str,
    s2: &str,
    order: SetLexOrder,
    operation: &str,
) -> Result<String, TranslateError> {
    let (lo, hi) = resolve_set_domain(ctx, s1, s2, operation)?;
    let aux = ctx.next_aux_id();
    let mut any1_next = "false".to_string();
    let mut any2_next = "false".to_string();
    let mut lex_next = match order {
        SetLexOrder::Less => "false".to_string(),
        SetLexOrder::LessEqual => "true".to_string(),
    };

    for value in (lo..=hi).rev() {
        let b1 = set_membership_term(ctx, s1, value, operation)?;
        let b2 = set_membership_term(ctx, s2, value, operation)?;
        let offset = i128::from(value) - i128::from(lo);
        let any1 = format!("_setlex{aux}_{offset}_any1");
        let any2 = format!("_setlex{aux}_{offset}_any2");
        let lex = format!("_setlex{aux}_{offset}_lex");

        ctx.emit_fmt(format_args!("(declare-const {any1} Bool)"));
        ctx.emit_fmt(format_args!("(declare-const {any2} Bool)"));
        ctx.emit_fmt(format_args!("(declare-const {lex} Bool)"));
        ctx.emit_fmt(format_args!("(assert (= {any1} (or {b1} {any1_next})))"));
        ctx.emit_fmt(format_args!("(assert (= {any2} (or {b2} {any2_next})))"));
        ctx.emit_fmt(format_args!(
            "(assert (= {lex} (or (and (= {b1} {b2}) {lex_next}) (and {b1} (not {b2}) {any2_next}) (and (not {b1}) {b2} (not {any1_next})))))"
        ));

        any1_next = any1;
        any2_next = any2;
        lex_next = lex;
    }

    Ok(lex_next)
}

/// `set_le(S1, S2)` → the sorted element list of S1 is lexicographically
/// less than or equal to that of S2.
pub(crate) fn set_le(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_le", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let condition = set_lex_condition(ctx, &s1, &s2, SetLexOrder::LessEqual, "set_le")?;
    ctx.emit_fmt(format_args!("(assert {condition})"));
    Ok(())
}

/// `set_lt(S1, S2)` → the sorted element list of S1 is lexicographically
/// less than that of S2.
pub(crate) fn set_lt(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_lt", args, 2)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let condition = set_lex_condition(ctx, &s1, &s2, SetLexOrder::Less, "set_lt")?;
    ctx.emit_fmt(format_args!("(assert {condition})"));
    Ok(())
}
