// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Set constraint handlers for FlatZinc-to-SMT-LIB translation.
// Encodes `var set of lo..hi` using boolean decomposition:
// width = hi-lo+1 boolean variables `name__bit__0` .. `name__bit__(width-1)`.
// Element i in S iff `S__bit__(i-lo)` is true.
//
// This avoids the ay model validation bug with mixed Int/BitVec theories.

use ay_flatzinc_parser::ast::Expr;

use crate::builtins::check_args;
use crate::error::TranslateError;
use crate::translate::{materialized_range_len, set_bit_name, Context, SmtInt};

/// Check whether element `e` is in a set literal (list of elements).
fn set_literal_contains(elements: &[i64], e: i64) -> bool {
    elements.contains(&e)
}

#[derive(Debug)]
enum SetArraySource {
    Param {
        lo: i64,
        hi: i64,
        sets: Vec<Vec<i64>>,
    },
    Vars {
        lo: i64,
        hi: i64,
        names: Vec<String>,
    },
}

impl SetArraySource {
    fn len(&self) -> usize {
        match self {
            Self::Param { sets, .. } => sets.len(),
            Self::Vars { names, .. } => names.len(),
        }
    }

    fn bounds(&self) -> (i64, i64) {
        match self {
            Self::Param { lo, hi, .. } | Self::Vars { lo, hi, .. } => (*lo, *hi),
        }
    }

    fn membership_terms(
        &self,
        ctx: &Context,
        elem: i64,
        opname: &str,
    ) -> Result<Vec<String>, TranslateError> {
        match self {
            Self::Param { sets, .. } => Ok(sets
                .iter()
                .map(|s| {
                    if set_literal_contains(s, elem) {
                        "true".to_string()
                    } else {
                        "false".to_string()
                    }
                })
                .collect()),
            Self::Vars { names, .. } => names
                .iter()
                .map(|name| set_membership_term(ctx, name, elem, opname))
                .collect(),
        }
    }

    /// Smallest contiguous value range that can contain a member of any source
    /// set. The caller applies the global materialization cap after unioning
    /// this with the result domain.
    fn value_bounds(
        &self,
        ctx: &Context,
        opname: &str,
    ) -> Result<Option<(i64, i64)>, TranslateError> {
        match self {
            Self::Param { sets, .. } => {
                let mut bounds: Option<(i64, i64)> = None;
                for value in sets.iter().flatten().copied() {
                    bounds = Some(match bounds {
                        Some((lo, hi)) => (lo.min(value), hi.max(value)),
                        None => (value, value),
                    });
                }
                Ok(bounds)
            }
            Self::Vars { names, .. } => {
                let mut bounds: Option<(i64, i64)> = None;
                for name in names {
                    let (lo, hi) = lookup_set_domain(ctx, name, opname)?;
                    if hi < lo {
                        continue;
                    }
                    bounds = Some(match bounds {
                        Some((union_lo, union_hi)) => (union_lo.min(lo), union_hi.max(hi)),
                        None => (lo, hi),
                    });
                }
                Ok(bounds)
            }
        }
    }
}

fn resolve_set_array_source(
    ctx: &Context,
    expr: &Expr,
    opname: &str,
) -> Result<SetArraySource, TranslateError> {
    match expr {
        Expr::Ident(name) => ctx
            .array_set_params
            .get(name)
            .map(|(lo, hi, sets)| SetArraySource::Param {
                lo: *lo,
                hi: *hi,
                sets: sets.clone(),
            })
            .or_else(|| {
                ctx.array_set_vars
                    .get(name)
                    .map(|(lo, hi, names)| SetArraySource::Vars {
                        lo: *lo,
                        hi: *hi,
                        names: names.clone(),
                    })
            })
            .ok_or_else(|| TranslateError::UnknownIdentifier(name.clone())),
        Expr::ArrayLit(elems) => elems
            .iter()
            .map(|elem| match elem {
                Expr::Ident(name) => {
                    lookup_set_domain(ctx, name, opname)?;
                    Ok(name.clone())
                }
                other => Err(TranslateError::UnsupportedType(format!(
                    "{opname}: expected set variable identifier in array literal, got {other:?}"
                ))),
            })
            .collect::<Result<Vec<_>, _>>()
            .and_then(|names| {
                let hi = i64::try_from(names.len()).map_err(|_| {
                    TranslateError::UnsupportedType(format!(
                        "{opname}: array literal is too large to index"
                    ))
                })?;
                Ok(SetArraySource::Vars { lo: 1, hi, names })
            }),
        _ => Err(TranslateError::ExpectedArray),
    }
}

fn lookup_set_domain(
    ctx: &Context,
    set_name: &str,
    opname: &str,
) -> Result<(i64, i64), TranslateError> {
    ctx.set_vars.get(set_name).copied().ok_or_else(|| {
        TranslateError::UnknownIdentifier(format!("{opname}: {set_name} is not a set var"))
    })
}

pub(crate) fn set_membership_term(
    ctx: &Context,
    set_name: &str,
    value: i64,
    opname: &str,
) -> Result<String, TranslateError> {
    let (lo, hi) = lookup_set_domain(ctx, set_name, opname)?;
    if value < lo || value > hi {
        Ok("false".to_string())
    } else {
        Ok(set_bit_name(set_name, (value - lo) as u32))
    }
}

fn resolve_set_domain3(
    ctx: &Context,
    s1: &str,
    s2: &str,
    s3: &str,
    name: &str,
) -> Result<(i64, i64), TranslateError> {
    let (lo1, hi1) = lookup_set_domain(ctx, s1, name)?;
    let (lo2, hi2) = lookup_set_domain(ctx, s2, name)?;
    let (lo3, hi3) = lookup_set_domain(ctx, s3, name)?;
    union_set_domains(&[(lo1, hi1), (lo2, hi2), (lo3, hi3)], name)
}

fn union_set_domains(
    domains: &[(i64, i64)],
    operation: &str,
) -> Result<(i64, i64), TranslateError> {
    let mut union: Option<(i64, i64)> = None;
    for &(lo, hi) in domains {
        if hi < lo {
            continue;
        }
        union = Some(match union {
            Some((union_lo, union_hi)) => (union_lo.min(lo), union_hi.max(hi)),
            None => (lo, hi),
        });
    }
    let (lo, hi) = union.unwrap_or((0, -1));
    materialized_range_len(lo, hi, operation)?;
    Ok((lo, hi))
}

/// `set_card(S, n)` → n = popcount(S)
/// Encodes as: n = sum of (ite S__bit__i 1 0) for each bit position.
pub(crate) fn set_card(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_card", args, 2)?;
    let s_name = ctx.expr_to_smt(&args[0])?;
    let n = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = ctx
        .set_vars
        .get(&s_name)
        .copied()
        .ok_or_else(|| TranslateError::UnknownIdentifier(s_name.clone()))?;
    let width = materialized_range_len(lo, hi, "set_card")?;

    let terms: Vec<String> = (0..width)
        .map(|i| {
            let bit = set_bit_name(&s_name, i as u32);
            format!("(ite {bit} 1 0)")
        })
        .collect();

    let sum = match terms.as_slice() {
        [] => "0".to_string(),
        [term] => term.clone(),
        _ => format!("(+ {})", terms.join(" ")),
    };

    ctx.emit_fmt(format_args!("(assert (= {n} {sum}))"));
    Ok(())
}

/// `set_union(S1, S2, S3)` → for each bit: S3_bit_i = S1_bit_i or S2_bit_i
pub(crate) fn set_union(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_union", args, 3)?;
    let s1 = ctx.expr_to_smt(&args[0])?;
    let s2 = ctx.expr_to_smt(&args[1])?;
    let s3 = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = resolve_set_domain3(ctx, &s1, &s2, &s3, "set_union")?;

    for value in lo..=hi {
        let b1 = set_membership_term(ctx, &s1, value, "set_union")?;
        let b2 = set_membership_term(ctx, &s2, value, "set_union")?;
        let b3 = set_membership_term(ctx, &s3, value, "set_union")?;
        ctx.emit_fmt(format_args!("(assert (= {b3} (or {b1} {b2})))"));
    }
    Ok(())
}

/// `set_in_reif(elem, set_var, bool)` where set_var is a set variable.
/// `elem` is a constant integer, `set_var` is a `var set of lo..hi`.
/// Encodes: bool iff S__bit__(elem-lo).
pub(crate) fn set_in_reif_var(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_in_reif", args, 3)?;
    let elem = ctx.resolve_int(&args[0])?;
    let s_name = ctx.expr_to_smt(&args[1])?;
    let b = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = ctx
        .set_vars
        .get(&s_name)
        .copied()
        .ok_or_else(|| TranslateError::UnknownIdentifier(s_name.clone()))?;

    if elem < lo || elem > hi {
        ctx.emit_fmt(format_args!("(assert (not {b}))"));
        return Ok(());
    }

    let bit_pos = (elem - lo) as u32;
    let membership = set_bit_name(&s_name, bit_pos);

    ctx.emit_fmt(format_args!("(assert (=> {b} {membership}))"));
    ctx.emit_fmt(format_args!("(assert (=> {membership} {b}))"));
    Ok(())
}

/// `set_in(x, S)` where S is a set variable and x is a variable integer.
/// Encodes: (or (and (= x lo) S__bit__0) (and (= x lo+1) S__bit__1) ...)
pub(crate) fn set_in_var(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("set_in", args, 2)?;
    let x = ctx.expr_to_smt(&args[0])?;
    let s_name = ctx.expr_to_smt(&args[1])?;

    let (lo, hi) = ctx
        .set_vars
        .get(&s_name)
        .copied()
        .ok_or_else(|| TranslateError::UnknownIdentifier(s_name.clone()))?;

    let conjuncts: Vec<String> = (lo..=hi)
        .map(|v| {
            let bit = set_bit_name(&s_name, (v - lo) as u32);
            format!("(and (= {x} {v}) {bit})")
        })
        .collect();

    match conjuncts.as_slice() {
        [] => ctx.emit("(assert false)"),
        [term] => ctx.emit_fmt(format_args!("(assert {term})")),
        _ => ctx.emit_fmt(format_args!("(assert (or {}))", conjuncts.join(" "))),
    }
    Ok(())
}

/// `array_set_element(idx, array, set_var)` where array is either a parameter
/// array of set literals or an inline array literal of set variables. For each
/// result bit, builds an ITE chain selecting membership at one-based `idx`.
pub(crate) fn array_set_element(ctx: &mut Context, args: &[Expr]) -> Result<(), TranslateError> {
    check_args("array_set_element", args, 3)?;
    let idx = ctx.expr_to_smt(&args[0])?;
    let s_result = ctx.expr_to_smt(&args[2])?;

    let (lo, hi) = ctx
        .set_vars
        .get(&s_result)
        .copied()
        .ok_or_else(|| TranslateError::UnknownIdentifier(s_result.clone()))?;
    let source = resolve_set_array_source(ctx, &args[1], "array_set_element")?;
    let n = source.len();
    if n == 0 {
        return Err(TranslateError::UnsupportedType(
            "array_set_element: empty array".into(),
        ));
    }

    let (array_lo, array_hi) = source.bounds();
    ctx.emit_fmt(format_args!(
        "(assert (and (>= {idx} {}) (<= {idx} {})))",
        SmtInt(array_lo),
        SmtInt(array_hi)
    ));

    // Equality must cover every value representable by either side. Restricting
    // this loop to the result domain would silently discard a selected source
    // member outside that domain and turn an impossible equality into SAT.
    let source_bounds = source.value_bounds(ctx, "array_set_element")?;
    let (value_lo, value_hi) = match source_bounds {
        Some(bounds) => union_set_domains(&[(lo, hi), bounds], "array_set_element")?,
        None => union_set_domains(&[(lo, hi)], "array_set_element")?,
    };

    // For each possible member, build an ITE chain selecting its membership.
    for elem_val in value_lo..=value_hi {
        let result_bit = set_membership_term(ctx, &s_result, elem_val, "array_set_element")?;
        let terms = source.membership_terms(ctx, elem_val, "array_set_element")?;

        let mut ite = terms[n - 1].clone();
        for i in (0..n - 1).rev() {
            let offset = i64::try_from(i).map_err(|_| {
                TranslateError::UnsupportedType(
                    "array_set_element: array index is too large".to_string(),
                )
            })?;
            let idx_val = array_lo.checked_add(offset).ok_or_else(|| {
                TranslateError::UnsupportedType(
                    "array_set_element: array index overflows i64".to_string(),
                )
            })?;
            ite = format!("(ite (= {idx} {}) {} {ite})", SmtInt(idx_val), terms[i]);
        }
        ctx.emit_fmt(format_args!("(assert (= {result_bit} {ite}))"));
    }
    Ok(())
}

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

#[cfg(test)]
#[path = "set_constraints_tests.rs"]
mod tests;
