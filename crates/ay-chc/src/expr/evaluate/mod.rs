// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Evaluation for CHC expressions.
//!
//! Display formatting is in `display.rs`. SmtValue comparison and array
//! evaluation helpers are in `value_ops.rs`.

mod display;
mod eval_bv;
mod value_ops;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

use super::{maybe_grow_expr_stack, ChcExpr, ChcOp, ExprDepthGuard};
use crate::bv_util::bv_mask;
use crate::smt::SmtValue;
use eval_bv::{
    big_bv_modulus, bigint_to_bv, eval_bv_ashr, eval_bv_big_val, eval_bv_binop, eval_bv_cmp,
    eval_bv_signed_div, eval_bv_signed_rem, eval_bv_smod, eval_bv_val, BvBinOp, BvCmpOp,
};

pub(crate) use value_ops::{eval_array_select, eval_int_big, eval_real_big, smt_values_equal};
// Re-export for tests (super::* glob) and internal use.
#[allow(unused_imports)]
pub(super) use value_ops::eval_array_store;
use value_ops::{eval_int_cmp, real_eval_enabled};

/// True when both operands are statically integer-sorted.
///
/// Used to route integer (dis)equalities through the widened `i128` evaluator
/// (`eval_int_cmp`) while leaving cross-sort equalities (e.g. the Bool/Int
/// coercion handled by `smt_values_equal`) on the canonical evaluator.
fn both_int_sorted(a: &ChcExpr, b: &ChcExpr) -> bool {
    a.sort() == super::ChcSort::Int && b.sort() == super::ChcSort::Int
}

/// Exact-rational (dis)equality fallback for the LRA lane.
///
/// Called only when the generic [`evaluate_expr`] path abstains on one side of
/// an `=`/`distinct` (typically because a side is a Real arithmetic tree the
/// generic arms do not fold). Both sides are evaluated exactly as
/// [`BigRational`](num_rational::BigRational); `want_eq` selects `=` vs `!=`.
/// Returns `None` (Indeterminate) when either side is not a fully-assigned
/// rational expression, preserving fail-closed behavior.
fn real_eq(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    want_eq: bool,
) -> Option<SmtValue> {
    if !real_eval_enabled() {
        return None;
    }
    let a = eval_real_big(lhs, model)?;
    let b = eval_real_big(rhs, model)?;
    Some(SmtValue::Bool((a == b) == want_eq))
}

fn eval_datatype_selector(
    name: &str,
    arg: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    // The subject only has to be a DATATYPE-SORTED expression that evaluates to
    // a datatype value; restricting it to `Var`/`FuncApp` made a selector over a
    // `select`, an `ite` or any other datatype-valued term indeterminate even
    // when the model decides it. The `SmtValue::Datatype` requirement below is
    // what keeps this exact.
    let super::ChcSort::Datatype { constructors, .. } = arg.sort() else {
        return None;
    };
    let SmtValue::Datatype(active_ctor, fields) = evaluate_expr(arg, model)? else {
        return None;
    };

    for ctor in constructors.iter() {
        if let Some((field_idx, _)) = ctor
            .selectors
            .iter()
            .enumerate()
            .find(|(_, selector)| selector.name == name)
        {
            if active_ctor == ctor.name {
                return fields.get(field_idx).cloned();
            }
            return None;
        }
    }

    None
}

fn eval_datatype_func_app(
    name: &str,
    sort: &super::ChcSort,
    args: &[Arc<ChcExpr>],
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    // SMT-LIB integer/real conversions are represented as `FuncApp` because
    // they are named operators rather than `ChcOp` variants.  Interpret only
    // their exact, well-sorted forms.  This is also needed when one of these
    // terms is an argument to an observed UF application: finite congruence
    // validation must compare the concrete argument values without treating
    // a conversion as an arbitrary UF.
    if args.len() == 1 && matches!(name, "to_real" | "to_int" | "is_int") {
        let argument = args[0].as_ref();
        match (name, sort, argument.sort(), evaluate_expr(argument, model)?) {
            ("to_real", super::ChcSort::Real, super::ChcSort::Int, SmtValue::Int(value)) => {
                return Some(SmtValue::Real(num_rational::BigRational::from_integer(
                    value.into(),
                )));
            }
            ("to_real", super::ChcSort::Real, super::ChcSort::Int, SmtValue::BigInt(value)) => {
                return Some(SmtValue::Real(num_rational::BigRational::from_integer(
                    value.as_ref().clone(),
                )));
            }
            // The converter deliberately accepts an already-Real coercion as
            // identity, so the evaluator mirrors that normalized form.
            ("to_real", super::ChcSort::Real, super::ChcSort::Real, SmtValue::Real(value)) => {
                return Some(SmtValue::Real(value));
            }
            ("to_int", super::ChcSort::Int, super::ChcSort::Real, SmtValue::Real(value)) => {
                return Some(SmtValue::int_from_bigint(value.floor().to_integer()));
            }
            ("to_int", super::ChcSort::Int, super::ChcSort::Int, SmtValue::Int(value)) => {
                return Some(SmtValue::Int(value));
            }
            ("to_int", super::ChcSort::Int, super::ChcSort::Int, SmtValue::BigInt(value)) => {
                return Some(SmtValue::BigInt(value));
            }
            ("is_int", super::ChcSort::Bool, super::ChcSort::Real, SmtValue::Real(value)) => {
                return Some(SmtValue::Bool(value.is_integer()));
            }
            (
                "is_int",
                super::ChcSort::Bool,
                super::ChcSort::Int,
                SmtValue::Int(_) | SmtValue::BigInt(_),
            ) => return Some(SmtValue::Bool(true)),
            _ => {}
        }
    }

    if let super::ChcSort::Datatype { constructors, .. } = sort {
        for ctor in constructors.iter() {
            if ctor.name == name && ctor.selectors.len() == args.len() {
                let fields = args
                    .iter()
                    .map(|arg| evaluate_expr(arg, model))
                    .collect::<Option<Vec<_>>>()?;
                return Some(SmtValue::Datatype(name.to_string(), fields));
            }
        }
    }

    if args.len() == 1 {
        let arg = args[0].as_ref();

        if let Some(rest) = name.strip_prefix("is-") {
            let SmtValue::Datatype(active_ctor, _) = evaluate_expr(arg, model)? else {
                return None;
            };
            return Some(SmtValue::Bool(active_ctor == rest));
        }

        if let Some(selector_value) = eval_datatype_selector(name, arg, model) {
            return Some(selector_value);
        }
    }

    None
}

/// Private marker carried by models that contain exact values for the finite
/// set of ordinary-UF applications observed in one executor query.
///
/// A marker is required before [`evaluate_expr`] consults the synthetic
/// application keys below.  Without it, a (programmatically constructed)
/// source variable whose name happened to equal one of those keys could be
/// mistaken for a function value in an unrelated model.
pub(crate) const UF_APPLICATION_MODEL_MARKER_KEY: &str = "\0ay.uf-application-model\0";
pub(crate) const UF_APPLICATION_MODEL_MARKER_VALUE: &str = "exact-v1";

/// Collision-free-with-SMT-source model key for one exact ordinary-UF term.
///
/// The NUL-prefixed key is never emitted as an SMT-LIB identifier.  The
/// executor paths store values under it only after reading dedicated fresh
/// aliases or exact post-SAT `get-value` observations. `Debug` is derived
/// structurally for `ChcExpr`, so equal application ASTs receive the same key
/// while distinct names/sorts/arguments remain distinct.
pub(crate) fn uf_application_model_key(expr: &ChcExpr) -> Option<String> {
    matches!(expr, ChcExpr::FuncApp(..)).then(|| format!("\0ay.uf-application-value:{expr:?}"))
}

fn scalar_uf_argument_key(value: &SmtValue) -> Option<String> {
    match value {
        SmtValue::Bool(value) => Some(format!("b:{value}")),
        SmtValue::Int(value) => Some(format!("i:{value}")),
        SmtValue::BigInt(value) => Some(format!("i:{}", value.as_ref())),
        SmtValue::Real(value) => Some(format!("r:{}/{}", value.numer(), value.denom())),
        SmtValue::BitVec(value, width) => Some(format!("bv:{width}:{value:x}")),
        SmtValue::BigBitVec(value, width) => Some(format!("bv:{width}:{}", value.to_str_radix(16))),
        SmtValue::Opaque(_)
        | SmtValue::ConstArray(_)
        | SmtValue::ArrayMap { .. }
        | SmtValue::Datatype(_, _) => None,
    }
}

/// Internal lookup key for a UF application normalized by its concrete scalar
/// arguments. This lets grounded witness replay evaluate `f(3)` from a solver
/// observation of a renamed/unrolled term such as `f(rule@2_x)` whose model
/// value is exactly `3`.
pub(crate) fn uf_application_concrete_model_key(
    expr: &ChcExpr,
    argument_values: &[SmtValue],
) -> Option<String> {
    let ChcExpr::FuncApp(name, return_sort, arguments) = expr else {
        return None;
    };
    if arguments.len() != argument_values.len() {
        return None;
    }
    let argument_sorts: Vec<super::ChcSort> = arguments.iter().map(|arg| arg.sort()).collect();
    let values = argument_values
        .iter()
        .map(scalar_uf_argument_key)
        .collect::<Option<Vec<_>>>()?;
    Some(format!(
        "\0ay.uf-concrete-application-value:{:?}",
        (name, return_sort, argument_sorts, values)
    ))
}

fn eval_observed_uf_application(
    expr: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    if !matches!(
        model.get(UF_APPLICATION_MODEL_MARKER_KEY),
        Some(SmtValue::Opaque(value)) if value == UF_APPLICATION_MODEL_MARKER_VALUE
    ) {
        return None;
    }
    if let Some(value) = model.get(&uf_application_model_key(expr)?) {
        return Some(value.clone());
    }
    let ChcExpr::FuncApp(_, _, arguments) = expr else {
        return None;
    };
    let argument_values = arguments
        .iter()
        .map(|argument| evaluate_expr(argument, model))
        .collect::<Option<Vec<_>>>()?;
    model
        .get(&uf_application_concrete_model_key(expr, &argument_values)?)
        .cloned()
}

/// Evaluate a CHC expression to an `SmtValue` under the given model.
///
/// Returns `None` when evaluation is indeterminate (missing variable,
/// unsupported operation like arrays/predicates, or arithmetic overflow).
/// Uses checked arithmetic and SMT-LIB Euclidean division/remainder semantics.
///
/// This is the single canonical evaluator for `ChcExpr`; all call sites in
/// PDR verification, model verification, and cube extraction delegate here.
pub(crate) fn evaluate_expr(
    expr: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    maybe_grow_expr_stack(|| {
        ExprDepthGuard::check()?;
        match expr {
            ChcExpr::Bool(b) => Some(SmtValue::Bool(*b)),
            ChcExpr::Int(n) => Some(SmtValue::Int(*n)),
            ChcExpr::BitVec(val, width) => Some(SmtValue::bitvec_from_u128(*val, *width)),
            // Real literal `num/den` → exact rational. Previously absent, so a
            // bare Real constant evaluated to `None` (Indeterminate); the LRA
            // model verifier could not validate any Real atom (#LRA-Lin gap).
            ChcExpr::Real(num, den) if *den != 0 && real_eval_enabled() => Some(SmtValue::Real(
                num_rational::BigRational::new((*num).into(), (*den).into()),
            )),
            ChcExpr::Var(v) => model.get(&v.name).cloned(),

            // Boolean connectives
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                match evaluate_expr(&args[0], model)? {
                    SmtValue::Bool(b) => Some(SmtValue::Bool(!b)),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::And, args) => {
                let mut all_determined = true;
                for arg in args {
                    match evaluate_expr(arg, model) {
                        Some(SmtValue::Bool(false)) => return Some(SmtValue::Bool(false)),
                        Some(SmtValue::Bool(true)) => {}
                        _ => all_determined = false,
                    }
                }
                if all_determined {
                    Some(SmtValue::Bool(true))
                } else {
                    None
                }
            }
            ChcExpr::Op(ChcOp::Or, args) => {
                let mut all_determined = true;
                for arg in args {
                    match evaluate_expr(arg, model) {
                        Some(SmtValue::Bool(true)) => return Some(SmtValue::Bool(true)),
                        Some(SmtValue::Bool(false)) => {}
                        _ => all_determined = false,
                    }
                }
                if all_determined {
                    Some(SmtValue::Bool(false))
                } else {
                    None
                }
            }
            ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                match (
                    evaluate_expr(&args[0], model),
                    evaluate_expr(&args[1], model),
                ) {
                    (Some(SmtValue::Bool(false)), _) => Some(SmtValue::Bool(true)),
                    (_, Some(SmtValue::Bool(true))) => Some(SmtValue::Bool(true)),
                    (Some(SmtValue::Bool(true)), Some(SmtValue::Bool(false))) => {
                        Some(SmtValue::Bool(false))
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Iff, args) if args.len() == 2 => {
                match (
                    evaluate_expr(&args[0], model),
                    evaluate_expr(&args[1], model),
                ) {
                    (Some(SmtValue::Bool(a)), Some(SmtValue::Bool(b))) => {
                        Some(SmtValue::Bool(a == b))
                    }
                    _ => None,
                }
            }

            // Comparisons (integer)
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Integer-sorted equalities go through the widened i128 evaluator
                // (see eval_int_cmp) so equalities against parser-encoded large
                // integer literals are decided correctly. Cross-sort / non-integer
                // operands fall back to smt_values_equal (Bool/Int coercion, etc.).
                if both_int_sorted(&args[0], &args[1]) {
                    return eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_eq);
                }
                match (
                    evaluate_expr(&args[0], model),
                    evaluate_expr(&args[1], model),
                ) {
                    (Some(a), Some(b)) => Some(SmtValue::Bool(smt_values_equal(&a, &b)?)),
                    // Real (LRA) lane: an operand is a Real arithmetic tree the
                    // generic evaluator cannot fold to a value. Compare exactly
                    // as rationals. Reached only when the generic path abstains.
                    _ => real_eq(&args[0], &args[1], model, true),
                }
            }
            ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
                if both_int_sorted(&args[0], &args[1]) {
                    return eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_ne);
                }
                match (
                    evaluate_expr(&args[0], model),
                    evaluate_expr(&args[1], model),
                ) {
                    (Some(a), Some(b)) => Some(SmtValue::Bool(!smt_values_equal(&a, &b)?)),
                    _ => real_eq(&args[0], &args[1], model, false),
                }
            }
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_lt)
            }
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_le)
            }
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_gt)
            }
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                eval_int_cmp(&args[0], &args[1], model, std::cmp::Ordering::is_ge)
            }

            // Arithmetic
            ChcExpr::Op(ChcOp::Add, args) => {
                // i128-lockstep: checked i128 arithmetic; overflow beyond i128
                // still degrades to None (Indeterminate), never wraps.
                let mut sum: i128 = 0;
                for arg in args {
                    match evaluate_expr(arg, model)? {
                        SmtValue::Int(n) => sum = sum.checked_add(n)?,
                        _ => return None,
                    }
                }
                Some(SmtValue::Int(sum))
            }
            ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                let first = match evaluate_expr(&args[0], model)? {
                    SmtValue::Int(n) => n,
                    _ => return None,
                };
                if args.len() == 1 {
                    return first.checked_neg().map(SmtValue::Int);
                }
                let mut result = first;
                for arg in &args[1..] {
                    match evaluate_expr(arg, model)? {
                        SmtValue::Int(n) => result = result.checked_sub(n)?,
                        _ => return None,
                    }
                }
                Some(SmtValue::Int(result))
            }
            ChcExpr::Op(ChcOp::Mul, args) => {
                let mut product: i128 = 1;
                for arg in args {
                    match evaluate_expr(arg, model)? {
                        SmtValue::Int(n) => product = product.checked_mul(n)?,
                        _ => return None,
                    }
                }
                Some(SmtValue::Int(product))
            }
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                match evaluate_expr(&args[0], model)? {
                    SmtValue::Int(n) => n.checked_neg().map(SmtValue::Int),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
                match (
                    evaluate_expr(&args[0], model)?,
                    evaluate_expr(&args[1], model)?,
                ) {
                    (SmtValue::Int(_), SmtValue::Int(0)) => {
                        // SMT-LIB total semantics: (div x 0) = 0
                        // Must match eliminate_mod (eliminate.rs).
                        Some(SmtValue::Int(0))
                    }
                    (SmtValue::Int(a), SmtValue::Int(b)) => {
                        // SMT-LIB div is Euclidean (remainder always non-negative)
                        a.checked_div_euclid(b).map(SmtValue::Int)
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                match (
                    evaluate_expr(&args[0], model)?,
                    evaluate_expr(&args[1], model)?,
                ) {
                    (SmtValue::Int(a), SmtValue::Int(0)) => {
                        // SMT-LIB total semantics: (mod x 0) = x
                        // Must match eliminate_mod (eliminate.rs).
                        Some(SmtValue::Int(a))
                    }
                    (SmtValue::Int(a), SmtValue::Int(b)) => {
                        a.checked_rem_euclid(b).map(SmtValue::Int)
                    }
                    _ => None,
                }
            }

            // ITE
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                match evaluate_expr(&args[0], model)? {
                    SmtValue::Bool(true) => evaluate_expr(&args[1], model),
                    SmtValue::Bool(false) => evaluate_expr(&args[2], model),
                    _ => None,
                }
            }

            // BV arithmetic
            ChcExpr::Op(ChcOp::BvAdd, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::Add)
            }
            ChcExpr::Op(ChcOp::BvSub, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::Sub)
            }
            ChcExpr::Op(ChcOp::BvMul, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::Mul)
            }
            ChcExpr::Op(ChcOp::BvUDiv, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::UDiv)
            }
            ChcExpr::Op(ChcOp::BvURem, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::URem)
            }
            ChcExpr::Op(ChcOp::BvSDiv, args) if args.len() == 2 => {
                eval_bv_signed_div(&args[0], &args[1], model)
            }
            ChcExpr::Op(ChcOp::BvSRem, args) if args.len() == 2 => {
                eval_bv_signed_rem(&args[0], &args[1], model)
            }
            ChcExpr::Op(ChcOp::BvSMod, args) if args.len() == 2 => {
                eval_bv_smod(&args[0], &args[1], model)
            }
            ChcExpr::Op(ChcOp::BvNeg, args) if args.len() == 1 => {
                if let Some((v, w)) = eval_bv_val(&args[0], model) {
                    return Some(SmtValue::BitVec((!v).wrapping_add(1) & bv_mask(w), w));
                }
                let (v, w) = eval_bv_big_val(&args[0], model)?;
                let result = if v == num_bigint::BigUint::from(0u8) {
                    v
                } else {
                    big_bv_modulus(w) - v
                };
                Some(SmtValue::bitvec_from_biguint(result, w))
            }

            // BV bitwise
            ChcExpr::Op(ChcOp::BvAnd, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::And)
            }
            ChcExpr::Op(ChcOp::BvOr, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::Or)
            }
            ChcExpr::Op(ChcOp::BvXor, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::Xor)
            }
            ChcExpr::Op(ChcOp::BvNand, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::Nand)
            }
            ChcExpr::Op(ChcOp::BvNor, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::Nor)
            }
            ChcExpr::Op(ChcOp::BvXnor, args) if args.len() == 2 => {
                eval_bv_binop(&args[0], &args[1], model, BvBinOp::Xnor)
            }
            ChcExpr::Op(ChcOp::BvNot, args) if args.len() == 1 => {
                if let Some((v, w)) = eval_bv_val(&args[0], model) {
                    return Some(SmtValue::BitVec((!v) & bv_mask(w), w));
                }
                let (v, w) = eval_bv_big_val(&args[0], model)?;
                Some(SmtValue::bitvec_from_biguint(
                    (big_bv_modulus(w) - num_bigint::BigUint::from(1u8)) ^ v,
                    w,
                ))
            }

            // BV shifts
            ChcExpr::Op(ChcOp::BvShl, args) if args.len() == 2 => {
                if let (Some((av, aw)), Some((bv, bw))) =
                    (eval_bv_val(&args[0], model), eval_bv_val(&args[1], model))
                {
                    if aw != bw {
                        return None;
                    }
                    let result = if bv >= u128::from(aw) {
                        0
                    } else {
                        (av << bv) & bv_mask(aw)
                    };
                    return Some(SmtValue::BitVec(result, aw));
                }
                let (av, aw) = eval_bv_big_val(&args[0], model)?;
                let (bv, bw) = eval_bv_big_val(&args[1], model)?;
                if aw != bw {
                    return None;
                }
                let result = if bv >= num_bigint::BigUint::from(aw) {
                    num_bigint::BigUint::from(0u8)
                } else {
                    av << num_traits::ToPrimitive::to_u32(&bv)?
                };
                Some(SmtValue::bitvec_from_biguint(result, aw))
            }
            ChcExpr::Op(ChcOp::BvLShr, args) if args.len() == 2 => {
                if let (Some((av, aw)), Some((bv, bw))) =
                    (eval_bv_val(&args[0], model), eval_bv_val(&args[1], model))
                {
                    if aw != bw {
                        return None;
                    }
                    let result = if bv >= u128::from(aw) { 0 } else { av >> bv };
                    return Some(SmtValue::BitVec(result, aw));
                }
                let (av, aw) = eval_bv_big_val(&args[0], model)?;
                let (bv, bw) = eval_bv_big_val(&args[1], model)?;
                if aw != bw {
                    return None;
                }
                let result = if bv >= num_bigint::BigUint::from(aw) {
                    num_bigint::BigUint::from(0u8)
                } else {
                    av >> num_traits::ToPrimitive::to_u32(&bv)?
                };
                Some(SmtValue::bitvec_from_biguint(result, aw))
            }
            ChcExpr::Op(ChcOp::BvAShr, args) if args.len() == 2 => {
                eval_bv_ashr(&args[0], &args[1], model)
            }

            // BV unsigned comparisons
            ChcExpr::Op(ChcOp::BvULt, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, BvCmpOp::Ult)
            }
            ChcExpr::Op(ChcOp::BvULe, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, BvCmpOp::Ule)
            }
            ChcExpr::Op(ChcOp::BvUGt, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, BvCmpOp::Ugt)
            }
            ChcExpr::Op(ChcOp::BvUGe, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, BvCmpOp::Uge)
            }

            // BV signed comparisons
            ChcExpr::Op(ChcOp::BvSLt, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, BvCmpOp::Slt)
            }
            ChcExpr::Op(ChcOp::BvSLe, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, BvCmpOp::Sle)
            }
            ChcExpr::Op(ChcOp::BvSGt, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, BvCmpOp::Sgt)
            }
            ChcExpr::Op(ChcOp::BvSGe, args) if args.len() == 2 => {
                eval_bv_cmp(&args[0], &args[1], model, BvCmpOp::Sge)
            }

            // BV comp (1-bit equality)
            ChcExpr::Op(ChcOp::BvComp, args) if args.len() == 2 => {
                let (av, aw) = eval_bv_big_val(&args[0], model)?;
                let (bv, bw) = eval_bv_big_val(&args[1], model)?;
                if aw != bw {
                    return None;
                }
                Some(SmtValue::BitVec(if av == bv { 1 } else { 0 }, 1))
            }

            // BV concat
            ChcExpr::Op(ChcOp::BvConcat, args) if args.len() == 2 => {
                let lhs = evaluate_expr(&args[0], model)?;
                let rhs = evaluate_expr(&args[1], model)?;
                if let (SmtValue::BitVec(av, aw), SmtValue::BitVec(bv, bw)) = (&lhs, &rhs) {
                    if *aw == 0 || *bw == 0 {
                        return None;
                    }
                    let new_w = aw.checked_add(*bw)?;
                    if new_w <= 128 {
                        // `bw == 128` can only pair with a zero-width lhs in
                        // this branch; its normalized payload is zero.
                        let av = *av & bv_mask(*aw);
                        let bv = *bv & bv_mask(*bw);
                        let shifted = if *bw == 128 { 0 } else { av << *bw };
                        let result = shifted | bv;
                        return Some(SmtValue::BitVec(result & bv_mask(new_w), new_w));
                    }
                }
                let (av, aw) = lhs.bitvec_to_biguint()?;
                let (bv, bw) = rhs.bitvec_to_biguint()?;
                if aw == 0 || bw == 0 {
                    return None;
                }
                let new_w = aw.checked_add(bw)?;
                if new_w == 0 || new_w > crate::MAX_BITVECTOR_WIDTH {
                    return None;
                }
                Some(SmtValue::bitvec_from_biguint((av << bw) | bv, new_w))
            }

            // BV extract
            ChcExpr::Op(ChcOp::BvExtract(hi, lo), args) if args.len() == 1 => {
                let (v, width) = eval_bv_big_val(&args[0], model)?;
                if hi < lo || *hi >= width {
                    return None;
                }
                let new_w = hi.checked_sub(*lo)?.checked_add(1)?;
                Some(SmtValue::bitvec_from_biguint(v >> *lo, new_w))
            }

            // BV zero_extend
            ChcExpr::Op(ChcOp::BvZeroExtend(n), args) if args.len() == 1 => {
                let (v, w) = eval_bv_big_val(&args[0], model)?;
                let new_w = w.checked_add(*n)?;
                if new_w > crate::MAX_BITVECTOR_WIDTH {
                    return None;
                }
                Some(SmtValue::bitvec_from_biguint(v, new_w))
            }

            // BV sign_extend
            ChcExpr::Op(ChcOp::BvSignExtend(n), args) if args.len() == 1 => {
                use num_bigint::BigUint;

                let (mut v, w) = eval_bv_big_val(&args[0], model)?;
                let new_w = w.checked_add(*n)?;
                if new_w > crate::MAX_BITVECTOR_WIDTH {
                    return None;
                }
                let sign_is_set =
                    w != 0 && ((&v >> (w - 1)) & BigUint::from(1u8)) == BigUint::from(1u8);
                if sign_is_set && new_w > w {
                    v |= (BigUint::from(1u8) << new_w) - (BigUint::from(1u8) << w);
                }
                Some(SmtValue::bitvec_from_biguint(v, new_w))
            }

            // BV rotate
            ChcExpr::Op(ChcOp::BvRotateLeft(n), args) if args.len() == 1 => {
                if let Some((v, w)) = eval_bv_val(&args[0], model) {
                    if w == 0 {
                        return Some(SmtValue::BitVec(0, w));
                    }
                    let rot = n % w;
                    if rot == 0 {
                        return Some(SmtValue::BitVec(v, w));
                    }
                    let result = ((v << rot) | (v >> (w - rot))) & bv_mask(w);
                    return Some(SmtValue::BitVec(result, w));
                }
                let (v, w) = eval_bv_big_val(&args[0], model)?;
                if w == 0 {
                    return Some(SmtValue::bitvec_from_biguint(v, w));
                }
                let rot = n % w;
                if rot == 0 {
                    return Some(SmtValue::bitvec_from_biguint(v, w));
                }
                let result = (&v << rot) | (v >> (w - rot));
                Some(SmtValue::bitvec_from_biguint(result, w))
            }
            ChcExpr::Op(ChcOp::BvRotateRight(n), args) if args.len() == 1 => {
                if let Some((v, w)) = eval_bv_val(&args[0], model) {
                    if w == 0 {
                        return Some(SmtValue::BitVec(0, w));
                    }
                    let rot = n % w;
                    if rot == 0 {
                        return Some(SmtValue::BitVec(v, w));
                    }
                    let result = ((v >> rot) | (v << (w - rot))) & bv_mask(w);
                    return Some(SmtValue::BitVec(result, w));
                }
                let (v, w) = eval_bv_big_val(&args[0], model)?;
                if w == 0 {
                    return Some(SmtValue::bitvec_from_biguint(v, w));
                }
                let rot = n % w;
                if rot == 0 {
                    return Some(SmtValue::bitvec_from_biguint(v, w));
                }
                let result = (&v >> rot) | (v << (w - rot));
                Some(SmtValue::bitvec_from_biguint(result, w))
            }

            // BV repeat
            ChcExpr::Op(ChcOp::BvRepeat(n), args) if args.len() == 1 => {
                let (v, w) = eval_bv_big_val(&args[0], model)?;
                let new_w = w.checked_mul(*n)?;
                if *n == 0 || new_w == 0 || new_w > crate::MAX_BITVECTOR_WIDTH {
                    return None;
                }
                let mut result = num_bigint::BigUint::from(0u8);
                for _ in 0..*n {
                    result = (result << w) | &v;
                }
                Some(SmtValue::bitvec_from_biguint(result, new_w))
            }

            // BV/Int conversions
            ChcExpr::Op(ChcOp::Bv2Nat, args) if args.len() == 1 => {
                let (v, _w) = eval_bv_big_val(&args[0], model)?;
                Some(SmtValue::int_from_bigint(num_bigint::BigInt::from(v)))
            }
            ChcExpr::Op(ChcOp::Int2Bv(w), args) if args.len() == 1 => {
                if *w == 0 || *w > crate::MAX_BITVECTOR_WIDTH {
                    return None;
                }
                if let Some(SmtValue::Int(n)) = evaluate_expr(&args[0], model) {
                    if *w <= 128 {
                        return Some(SmtValue::BitVec((n as u128) & bv_mask(*w), *w));
                    }
                }
                let value = eval_int_big(&args[0], model)?;
                Some(SmtValue::bitvec_from_biguint(bigint_to_bv(value, *w), *w))
            }

            // Array select: select(arr, idx) → look up idx in array value
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                let arr_val = evaluate_expr(&args[0], model)?;
                let idx_val = evaluate_expr(&args[1], model)?;
                eval_array_select(&arr_val, &idx_val)
            }

            // Array store: store(arr, idx, val) → insert/overwrite in array value
            ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                let arr_val = evaluate_expr(&args[0], model)?;
                let idx_val = evaluate_expr(&args[1], model)?;
                let elem_val = evaluate_expr(&args[2], model)?;
                Some(eval_array_store(arr_val, idx_val, elem_val))
            }

            // Constant array: ((as const (Array K V)) val)
            ChcExpr::ConstArray(_key_sort, val) => {
                let v = evaluate_expr(val, model)?;
                Some(SmtValue::ConstArray(Box::new(v)))
            }

            ChcExpr::FuncApp(name, sort, args) => eval_datatype_func_app(name, sort, args, model)
                .or_else(|| eval_observed_uf_application(expr, model)),

            // Predicates, functions, etc. - cannot evaluate
            _ => None,
        }
    })
}

#[cfg(test)]
mod tests;
