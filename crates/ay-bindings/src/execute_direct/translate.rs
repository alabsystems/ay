// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use std::collections::BTreeMap;

use ay_dpll::api::{Sort as ApiSort, Term};

use super::context::{expr_solver_op, ExecutionContext};
use super::translate_bridge;
use super::ExecuteError;
use crate::expr::{Expr, ExprValue};
use crate::sort::{Sort, SortInner};

/// Red zone size for `stacker::maybe_grow` in expression translation.
///
/// QuantifierConsumer's datatype-heavy ADT verification tests create deeply nested Expr
/// trees that overflow the default thread stack (8MB) during recursive
/// translation. This guard ensures the stack is grown on demand (#8414).
const TRANSLATE_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024 // 128 KB in debug (frames are larger)
} else {
    32 * 1024 // 32 KB in release
};

/// Stack size to allocate when the red zone is hit during translation.
const TRANSLATE_STACK_SIZE: usize = 2 * 1024 * 1024; // 2 MB

/// Translate ay_bindings::Sort to ay_dpll::api::Sort.
///
/// Uses the From impl from sort.rs for supported sorts. Datatype sorts
/// are translated to `Sort::Uninterpreted(name)` which is how the SMT-LIB
/// parser represents declared datatypes internally.
pub(super) fn translate_sort(sort: &Sort) -> Result<ApiSort, ExecuteError> {
    match sort.inner() {
        // Datatype sorts map to Uninterpreted(name) — the DeclareDatatype
        // constraint registers the actual DT structure with the solver.
        SortInner::Datatype(dt) => Ok(ay_core::Sort::Uninterpreted(dt.name.clone())),
        _ => Ok(ay_core::Sort::from(sort)),
    }
}

/// Bridge a ay_bindings DatatypeSort to ay_core DatatypeSort.
///
/// Both crates define identical DatatypeSort structures but with different
/// Sort types for fields. This function converts by translating each field sort.
pub(super) fn bridge_datatype(
    dt: &crate::sort::DatatypeSort,
) -> Result<ay_core::DatatypeSort, ExecuteError> {
    let constructors = dt
        .constructors
        .iter()
        .map(|ctor| {
            let fields: Result<Vec<_>, _> = ctor
                .fields
                .iter()
                .map(|f| {
                    let sort = translate_sort(&f.sort)?;
                    Ok(ay_core::DatatypeField::new(&f.name, sort))
                })
                .collect();
            Ok(ay_core::DatatypeConstructor::new(&ctor.name, fields?))
        })
        .collect::<Result<Vec<_>, ExecuteError>>()?;
    Ok(ay_core::DatatypeSort::new(&dt.name, constructors))
}

/// Translate ay_bindings::Expr to ay_dpll::api::Term.
///
/// Uses `stacker::maybe_grow` for stack safety on deeply nested expressions (#8414).
pub(super) fn translate_expr(
    ctx: &mut ExecutionContext,
    expr: &Expr,
) -> Result<Term, ExecuteError> {
    stacker::maybe_grow(TRANSLATE_STACK_RED_ZONE, TRANSLATE_STACK_SIZE, || {
        translate_expr_inner(ctx, expr)
    })
}

/// Inner translation logic, called within stacker guard.
fn translate_expr_inner(ctx: &mut ExecutionContext, expr: &Expr) -> Result<Term, ExecuteError> {
    if let Some(result) = translate_bridge::maybe_translate_expr(ctx, expr) {
        return result;
    }

    match expr.value() {
        // Constants
        ExprValue::BoolConst(b) => Ok(ctx.solver.bool_const(*b)),

        ExprValue::BitVecConst { value, width } => expr_solver_op(
            ctx.solver.try_bv_const_bigint(value, *width),
            "bv_const_bigint",
        ),

        ExprValue::IntConst(value) => Ok(ctx.solver.int_const_bigint(value)),

        ExprValue::RealConst(value) => {
            // RealConst is an integer value in Real context.
            // Use rational_const_bigint to avoid precision loss via f64 (#5427).
            let one = num_bigint::BigInt::from(1);
            expr_solver_op(
                ctx.solver.try_rational_const_bigint(value, &one),
                "rational_const_bigint",
            )
        }

        // Variables
        ExprValue::Var { name } => {
            // String constants are represented as Var with quoted name and String sort.
            // Detect this pattern and translate to solver.string_const() (#5969).
            if expr.sort().is_string() && name.starts_with('"') && name.ends_with('"') {
                let unquoted = &name[1..name.len() - 1];
                return Ok(ctx.solver.string_const(unquoted));
            }
            ctx.lookup_var(name).ok_or_else(|| {
                ExecuteError::ExprTranslation(format!("undefined variable: {}", name))
            })
        }

        // Packet 1C bridge variants are translated centrally in
        // execute_direct::translate_bridge. Reaching this fallback match for any
        // of them means the shared bridge regressed.
        ExprValue::Not(_)
        | ExprValue::And(_)
        | ExprValue::Or(_)
        | ExprValue::Xor(_, _)
        | ExprValue::Implies(_, _)
        | ExprValue::Ite { .. }
        | ExprValue::Eq(_, _)
        | ExprValue::Distinct(_)
        | ExprValue::IntAdd(_, _)
        | ExprValue::IntSub(_, _)
        | ExprValue::IntMul(_, _)
        | ExprValue::IntDiv(_, _)
        | ExprValue::IntMod(_, _)
        | ExprValue::IntNeg(_)
        | ExprValue::IntLt(_, _)
        | ExprValue::IntLe(_, _)
        | ExprValue::IntGt(_, _)
        | ExprValue::IntGe(_, _)
        | ExprValue::BvAdd(_, _)
        | ExprValue::BvSub(_, _)
        | ExprValue::BvMul(_, _)
        | ExprValue::BvULt(_, _)
        | ExprValue::BvSLt(_, _)
        | ExprValue::Select { .. }
        | ExprValue::Store { .. }
        | ExprValue::ConstArray { .. }
        | ExprValue::BvUDiv(_, _)
        | ExprValue::BvSDiv(_, _)
        | ExprValue::BvURem(_, _)
        | ExprValue::BvSRem(_, _)
        | ExprValue::BvNeg(_)
        | ExprValue::BvNot(_)
        | ExprValue::BvAnd(_, _)
        | ExprValue::BvOr(_, _)
        | ExprValue::BvXor(_, _)
        | ExprValue::BvShl(_, _)
        | ExprValue::BvLShr(_, _)
        | ExprValue::BvAShr(_, _)
        | ExprValue::BvULe(_, _)
        | ExprValue::BvUGt(_, _)
        | ExprValue::BvUGe(_, _)
        | ExprValue::BvSLe(_, _)
        | ExprValue::BvSGt(_, _)
        | ExprValue::BvSGe(_, _)
        | ExprValue::BvZeroExtend { .. }
        | ExprValue::BvSignExtend { .. }
        | ExprValue::BvExtract { .. }
        | ExprValue::BvConcat(_, _)
        | ExprValue::BvAddNoOverflowUnsigned(_, _)
        | ExprValue::BvAddNoOverflowSigned(_, _)
        | ExprValue::BvSubNoUnderflowUnsigned(_, _)
        | ExprValue::BvSubNoOverflowSigned(_, _)
        | ExprValue::BvMulNoOverflowUnsigned(_, _)
        | ExprValue::BvMulNoOverflowSigned(_, _)
        | ExprValue::BvNegNoOverflow(_)
        | ExprValue::BvSdivNoOverflow(_, _)
        | ExprValue::StrConcat(_, _)
        | ExprValue::StrLen(_)
        | ExprValue::StrAt(_, _)
        | ExprValue::StrSubstr(_, _, _)
        | ExprValue::StrContains(_, _)
        | ExprValue::StrPrefixOf(_, _)
        | ExprValue::StrSuffixOf(_, _)
        | ExprValue::StrIndexOf(_, _, _)
        | ExprValue::StrReplace(_, _, _)
        | ExprValue::StrReplaceAll(_, _, _)
        | ExprValue::StrToInt(_)
        | ExprValue::StrFromInt(_)
        | ExprValue::StrToRe(_)
        | ExprValue::StrInRe(_, _)
        | ExprValue::ReStar(_)
        | ExprValue::RePlus(_)
        | ExprValue::ReUnion(_, _)
        | ExprValue::ReConcat(_, _)
        | ExprValue::SeqEmpty(_)
        | ExprValue::SeqUnit(_)
        | ExprValue::SeqConcat(_, _)
        | ExprValue::SeqLen(_)
        | ExprValue::SeqNth(_, _)
        | ExprValue::SeqExtract(_, _, _)
        | ExprValue::SeqContains(_, _)
        | ExprValue::SeqPrefixOf(_, _)
        | ExprValue::SeqSuffixOf(_, _)
        | ExprValue::SeqIndexOf(_, _, _)
        | ExprValue::SeqReplace(_, _, _)
        | ExprValue::FuncApp { .. } => Err(ExecuteError::Internal(format!(
            "translate_bridge did not handle bridged expression: {}",
            expr
        ))),

        // Note: Real arithmetic (RealAdd, RealSub, RealMul, RealDiv, RealNeg,
        // Real comparison operations (RealLt, RealLe, RealGt, RealGe) are implemented
        // via ay's generic API but have known issues with model validation.
        // IntToReal conversion also requires SMT-LIB2 fallback.
        // When Real operations are fixed, expr_fallback_reason() can be updated to
        // only fall back for IntToReal.

        // Bv2Int — supported via ay_dpll try API (#5406, #5140)
        ExprValue::Bv2Int(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_bv2int(t), "bv2int")
        }

        // Datatype operations — bridged to ay_dpll DT API (#5404)
        ExprValue::DatatypeConstructor {
            datatype_name,
            constructor_name,
            args,
        } => {
            let core_dt = ctx
                .declared_datatypes
                .get(datatype_name)
                .ok_or_else(|| {
                    ExecuteError::ExprTranslation(format!(
                        "undeclared datatype '{}' in constructor application",
                        datatype_name
                    ))
                })?
                .clone();
            let translated_args: Result<Vec<_>, _> =
                args.iter().map(|a| translate_expr(ctx, a)).collect();
            ctx.solver
                .try_datatype_constructor(&core_dt, constructor_name, &translated_args?)
                .map_err(|e| ExecuteError::ExprTranslation(e.to_string()))
        }
        ExprValue::DatatypeSelector {
            selector_name,
            expr: inner,
            ..
        } => {
            let translated = translate_expr(ctx, inner)?;
            let result_sort = translate_sort(&expr.sort())?;
            ctx.solver
                .try_datatype_selector(selector_name, translated, result_sort)
                .map_err(|e| ExecuteError::ExprTranslation(e.to_string()))
        }
        ExprValue::DatatypeTester {
            constructor_name,
            expr: inner,
            ..
        } => {
            let translated = translate_expr(ctx, inner)?;
            ctx.solver
                .try_datatype_tester(constructor_name, translated)
                .map_err(|e| ExecuteError::ExprTranslation(e.to_string()))
        }

        // Quantifiers — supported via ay_dpll forall/exists API (#5406)
        ExprValue::Forall {
            vars,
            body,
            triggers,
        } => translate_quantifier(ctx, vars, body, triggers, true),
        ExprValue::Exists {
            vars,
            body,
            triggers,
        } => translate_quantifier(ctx, vars, body, triggers, false),

        // Sort conversions — supported via ay_dpll try API (#5406, #5140)
        ExprValue::IntToReal(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_int_to_real(t), "int_to_real")
        }
        ExprValue::RealToInt(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_real_to_int(t), "real_to_int")
        }
        ExprValue::IsInt(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_is_int(t), "is_int")
        }

        // Real arithmetic - uses ay's generic try API (#993, #5140)
        ExprValue::RealAdd(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_add(ta, tb), "add")
        }
        ExprValue::RealSub(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_sub(ta, tb), "sub")
        }
        ExprValue::RealMul(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_mul(ta, tb), "mul")
        }
        ExprValue::RealDiv(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            // Use generic try_div() - works for both Int and Real sorts (#993)
            expr_solver_op(ctx.solver.try_div(ta, tb), "div")
        }
        ExprValue::RealNeg(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_neg(t), "neg")
        }

        // Real comparisons - uses ay's generic try API (#993, #5140)
        ExprValue::RealLt(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_lt(ta, tb), "lt")
        }
        ExprValue::RealLe(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_le(ta, tb), "le")
        }
        ExprValue::RealGt(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_gt(ta, tb), "gt")
        }
        ExprValue::RealGe(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_ge(ta, tb), "ge")
        }

        // Int2Bv — supported via ay_dpll try API (#5406, #5140)
        ExprValue::Int2Bv(inner, width) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_int2bv(t, *width), "int2bv")
        }

        // --- FP constants (#5774) ---
        ExprValue::FpPlusInfinity { eb, sb } => Ok(ctx.solver.fp_plus_infinity(*eb, *sb)),
        ExprValue::FpMinusInfinity { eb, sb } => Ok(ctx.solver.fp_minus_infinity(*eb, *sb)),
        ExprValue::FpNaN { eb, sb } => Ok(ctx.solver.fp_nan(*eb, *sb)),
        ExprValue::FpPlusZero { eb, sb } => Ok(ctx.solver.fp_plus_zero(*eb, *sb)),
        ExprValue::FpMinusZero { eb, sb } => Ok(ctx.solver.fp_minus_zero(*eb, *sb)),

        // --- FP unary ops (#5774, #5140) ---
        ExprValue::FpAbs(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_abs(t), "fp_abs")
        }
        ExprValue::FpNeg(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_neg(t), "fp_neg")
        }

        // --- FP comparisons (#5774, #5140) ---
        ExprValue::FpEq(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_eq(ta, tb), "fp_eq")
        }
        ExprValue::FpLt(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_lt(ta, tb), "fp_lt")
        }
        ExprValue::FpLe(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_le(ta, tb), "fp_le")
        }
        ExprValue::FpGt(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_gt(ta, tb), "fp_gt")
        }
        ExprValue::FpGe(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_ge(ta, tb), "fp_ge")
        }

        // --- FP classification predicates (#5774, #5140) ---
        ExprValue::FpIsNaN(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_is_nan(t), "fp_is_nan")
        }
        ExprValue::FpIsInfinite(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_is_infinite(t), "fp_is_infinite")
        }
        ExprValue::FpIsZero(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_is_zero(t), "fp_is_zero")
        }
        ExprValue::FpIsNormal(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_is_normal(t), "fp_is_normal")
        }
        ExprValue::FpIsSubnormal(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_is_subnormal(t), "fp_is_subnormal")
        }
        ExprValue::FpIsPositive(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_is_positive(t), "fp_is_positive")
        }
        ExprValue::FpIsNegative(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_is_negative(t), "fp_is_negative")
        }

        // --- FP min/max (#5774, #5140) ---
        ExprValue::FpMin(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_min(ta, tb), "fp_min")
        }
        ExprValue::FpMax(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_max(ta, tb), "fp_max")
        }

        // --- FP conversions (#5774, #5140) ---
        ExprValue::FpToReal(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_to_real(t), "fp_to_real")
        }
        ExprValue::FpToIeeeBv(inner) => {
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_to_ieee_bv(t), "fp_to_ieee_bv")
        }
        ExprValue::FpToSbv(rm, inner, width) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_to_sbv(rm_term, t, *width), "fp_to_sbv")
        }
        ExprValue::FpToUbv(rm, inner, width) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_to_ubv(rm_term, t, *width), "fp_to_ubv")
        }
        ExprValue::FpFromBvs(sign, exp, sig) => {
            let ts = translate_expr(ctx, sign)?;
            let te = translate_expr(ctx, exp)?;
            let tg = translate_expr(ctx, sig)?;
            // Infer eb/sb from the expression's sort.
            let fp_sort = translate_sort(expr.sort())?;
            match fp_sort {
                ay_core::Sort::FloatingPoint(eb, sb) => expr_solver_op(
                    ctx.solver.try_fp_from_bvs(ts, te, tg, eb, sb),
                    "fp_from_bvs",
                ),
                _ => Err(ExecuteError::ExprTranslation(
                    "FpFromBvs expression has non-FP sort".to_string(),
                )),
            }
        }
        ExprValue::BvToFp(rm, inner, eb, sb) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_bv_to_fp(rm_term, t, *eb, *sb), "bv_to_fp")
        }
        ExprValue::BvToFpUnsigned(rm, inner, eb, sb) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(
                ctx.solver.try_bv_to_fp_unsigned(rm_term, t, *eb, *sb),
                "bv_to_fp_unsigned",
            )
        }
        ExprValue::FpToFp(rm, inner, eb, sb) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_to_fp(rm_term, t, *eb, *sb), "fp_to_fp")
        }

        // --- FP arithmetic (#6128, #5140) ---
        // All 8 FP arithmetic operations are fully bit-blasted in ay-dpll.
        // Previously forced through SMT-LIB fallback; now wired directly.
        ExprValue::FpAdd(rm, a, b) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_add(rm_term, ta, tb), "fp_add")
        }
        ExprValue::FpSub(rm, a, b) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_sub(rm_term, ta, tb), "fp_sub")
        }
        ExprValue::FpMul(rm, a, b) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_mul(rm_term, ta, tb), "fp_mul")
        }
        ExprValue::FpDiv(rm, a, b) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_div(rm_term, ta, tb), "fp_div")
        }
        ExprValue::FpFma(rm, a, b, c) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            let tc = translate_expr(ctx, c)?;
            expr_solver_op(ctx.solver.try_fp_fma(rm_term, ta, tb, tc), "fp_fma")
        }
        ExprValue::FpSqrt(rm, inner) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(ctx.solver.try_fp_sqrt(rm_term, t), "fp_sqrt")
        }
        ExprValue::FpRem(a, b) => {
            let ta = translate_expr(ctx, a)?;
            let tb = translate_expr(ctx, b)?;
            expr_solver_op(ctx.solver.try_fp_rem(ta, tb), "fp_rem")
        }
        ExprValue::FpRoundToIntegral(rm, inner) => {
            let rm_term = expr_solver_op(
                ctx.solver.try_fp_rounding_mode(rm.smt_name()),
                "fp_rounding_mode",
            )?;
            let t = translate_expr(ctx, inner)?;
            expr_solver_op(
                ctx.solver.try_fp_round_to_integral(rm_term, t),
                "fp_round_to_integral",
            )
        }
    }
}

/// Translate a quantifier (forall or exists) to ay_dpll terms.
///
/// Creates bound variables via `declare_const`, translates the body with those
/// variables in scope, then builds the quantifier term (with optional triggers).
/// Restores the variable scope afterward to avoid leaking bound variables.
fn translate_quantifier(
    ctx: &mut ExecutionContext,
    vars: &[(String, Sort)],
    body: &Expr,
    triggers: &[Vec<Expr>],
    is_forall: bool,
) -> Result<Term, ExecuteError> {
    // Save existing variable bindings so we can restore them after.
    // translate_sort can fail before any scope mutation, so do it first.
    let api_sorts: Vec<_> = vars
        .iter()
        .map(|(_, sort)| translate_sort(sort))
        .collect::<Result<_, _>>()?;

    let mut scope = BTreeMap::new();
    let mut var_terms = Vec::with_capacity(vars.len());

    for ((name, _), api_sort) in vars.iter().zip(api_sorts) {
        let term = ctx.solver.declare_const(name, api_sort);
        scope.insert(name.clone(), term);
        var_terms.push(term);
    }

    ctx.bound_var_scopes.push(scope);

    // Build quantifier body and triggers. Scope must be restored on ALL paths.
    let result = translate_quantifier_inner(ctx, &var_terms, body, triggers, is_forall);

    ctx.bound_var_scopes.pop();

    result
}

/// Inner helper for translate_quantifier — separated so the caller can
/// unconditionally restore scope after this returns (success or error).
fn translate_quantifier_inner(
    ctx: &mut ExecutionContext,
    var_terms: &[Term],
    body: &Expr,
    triggers: &[Vec<Expr>],
    is_forall: bool,
) -> Result<Term, ExecuteError> {
    let body_term = translate_expr(ctx, body)?;

    if triggers.is_empty() {
        if is_forall {
            ctx.solver
                .try_forall(var_terms, body_term)
                .map_err(|e| ExecuteError::ExprTranslation(e.to_string()))
        } else {
            ctx.solver
                .try_exists(var_terms, body_term)
                .map_err(|e| ExecuteError::ExprTranslation(e.to_string()))
        }
    } else {
        let mut trigger_terms: Vec<Vec<Term>> = Vec::with_capacity(triggers.len());
        for pattern in triggers {
            let terms: Result<Vec<_>, _> = pattern.iter().map(|e| translate_expr(ctx, e)).collect();
            trigger_terms.push(terms?);
        }
        let trigger_refs: Vec<&[Term]> = trigger_terms.iter().map(|t| t.as_slice()).collect();
        if is_forall {
            ctx.solver
                .try_forall_with_triggers(var_terms, body_term, &trigger_refs)
                .map_err(|e| ExecuteError::ExprTranslation(e.to_string()))
        } else {
            ctx.solver
                .try_exists_with_triggers(var_terms, body_term, &trigger_refs)
                .map_err(|e| ExecuteError::ExprTranslation(e.to_string()))
        }
    }
}
