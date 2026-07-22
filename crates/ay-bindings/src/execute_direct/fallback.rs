// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Fallback detection for direct execution.
//!
//! These functions check if a AYProgram can be executed via the direct
//! ay_dpll API or needs to fall back to SMT-LIB file-based execution.

use super::{ExecuteFallback, ExecuteFallbackKind};
use crate::constraint::Constraint;
use crate::expr::{Expr, ExprValue};
use crate::program::AYProgram;

/// Check if the program needs fallback to SMT-LIB path.
pub(crate) fn needs_fallback(program: &AYProgram) -> Option<ExecuteFallback> {
    // Check for unsupported commands
    for constraint in program.commands() {
        match constraint {
            Constraint::SoftAssert { .. } => {
                return Some(ExecuteFallback {
                    kind: ExecuteFallbackKind::SoftAssertions,
                    message: "program contains soft assertions".to_string(),
                });
            }
            // OMT commands (Maximize, Minimize, GetObjectives) are handled by
            // the OMT executor bridge (#6702) — no longer a fallback condition.
            Constraint::Maximize(_) | Constraint::Minimize(_) | Constraint::GetObjectives => {}
            Constraint::DeclareRel { .. } => {
                return Some(ExecuteFallback {
                    kind: ExecuteFallbackKind::ChcRelationDeclaration,
                    message: "program contains CHC relation declaration".to_string(),
                });
            }
            Constraint::Rule { .. } => {
                return Some(ExecuteFallback {
                    kind: ExecuteFallbackKind::ChcRule,
                    message: "program contains CHC rule".to_string(),
                });
            }
            Constraint::Query(_) => {
                return Some(ExecuteFallback {
                    kind: ExecuteFallbackKind::ChcQuery,
                    message: "program contains CHC query".to_string(),
                });
            }
            // CheckSatAssuming is now handled directly (#5456). Assumptions
            // are collected during constraint processing and passed to
            // solver.check_sat_assuming() at the end.
            Constraint::CheckSatAssuming(_) => {}
            // GetValue is now supported (#1977) - terms are collected during constraint
            // processing and evaluated after check-sat returns SAT.
            _ => {}
        }

        if let Some(reason) = constraint_expr_fallback_reason(constraint) {
            return Some(reason);
        }
    }

    None
}

/// Check if the program contains optimization objectives (maximize/minimize).
pub(crate) fn contains_objectives(program: &AYProgram) -> bool {
    program.commands().iter().any(|c| {
        matches!(
            c,
            Constraint::Maximize(_) | Constraint::Minimize(_) | Constraint::GetObjectives
        )
    })
}

fn constraint_expr_fallback_reason(constraint: &Constraint) -> Option<ExecuteFallback> {
    let reason = match constraint {
        Constraint::Assert { expr, .. } => expr_fallback_reason(expr),
        Constraint::DefineFun { body, .. } => expr_fallback_reason(body),
        Constraint::SoftAssert { expr, .. } => expr_fallback_reason(expr),
        // CheckSatAssuming is handled directly (#5456) but we still check its
        // assumption expressions for fallback reasons (e.g., large BV constants).
        // GetValue is now supported (#1977) and passes through to direct execution.
        Constraint::CheckSatAssuming(exprs) | Constraint::GetValue(exprs) => {
            exprs.iter().find_map(expr_fallback_reason)
        }
        Constraint::Rule { head, body } => {
            if let Some(head_expr) = head {
                if let Some(r) = expr_fallback_reason(head_expr) {
                    return Some(ExecuteFallback {
                        kind: ExecuteFallbackKind::UnsupportedExpression,
                        message: r,
                    });
                }
            }
            expr_fallback_reason(body)
        }
        Constraint::Query(expr) => expr_fallback_reason(expr),
        Constraint::Maximize(expr) | Constraint::Minimize(expr) => expr_fallback_reason(expr),
        _ => None,
    };
    reason.map(|message| ExecuteFallback {
        kind: ExecuteFallbackKind::UnsupportedExpression,
        message,
    })
}

fn expr_fallback_reason(expr: &Expr) -> Option<String> {
    stacker::maybe_grow(32 * 1024, 1024 * 1024, || expr_fallback_reason_inner(expr))
}

fn expr_fallback_reason_inner(expr: &Expr) -> Option<String> {
    match expr.value() {
        ExprValue::BoolConst(_) | ExprValue::Var { .. } => None,
        // All constant types use BigInt-capable APIs (bv_const_bigint,
        // int_const_bigint, rational_const_bigint) so no fallback needed
        // for large values including 128-bit BV constants.
        ExprValue::BitVecConst { .. } | ExprValue::IntConst(_) | ExprValue::RealConst(_) => None,
        // Unary — traverse single subexpression
        ExprValue::Not(inner)
        | ExprValue::IntNeg(inner)
        | ExprValue::BvNeg(inner)
        | ExprValue::BvNot(inner)
        | ExprValue::BvNegNoOverflow(inner)
        | ExprValue::IntToReal(inner)
        | ExprValue::RealToInt(inner)
        | ExprValue::IsInt(inner)
        | ExprValue::RealNeg(inner)
        | ExprValue::Bv2Int(inner)
        | ExprValue::ConstArray { value: inner, .. } => expr_fallback_reason(inner),
        ExprValue::Int2Bv(inner, _) => expr_fallback_reason(inner),
        ExprValue::BvZeroExtend { expr: inner, .. }
        | ExprValue::BvSignExtend { expr: inner, .. }
        | ExprValue::BvExtract { expr: inner, .. }
        | ExprValue::DatatypeSelector { expr: inner, .. }
        | ExprValue::DatatypeTester { expr: inner, .. } => expr_fallback_reason(inner),
        // N-ary — traverse all args
        ExprValue::And(args)
        | ExprValue::Or(args)
        | ExprValue::Distinct(args)
        | ExprValue::DatatypeConstructor { args, .. }
        | ExprValue::FuncApp { args, .. } => args.iter().find_map(expr_fallback_reason),
        // Ternary
        ExprValue::Ite {
            cond,
            then_expr,
            else_expr,
        } => expr_fallback_reason(cond)
            .or_else(|| expr_fallback_reason(then_expr))
            .or_else(|| expr_fallback_reason(else_expr)),
        ExprValue::Store {
            array,
            index,
            value,
        } => expr_fallback_reason(array)
            .or_else(|| expr_fallback_reason(index))
            .or_else(|| expr_fallback_reason(value)),
        // Binary array
        ExprValue::Select { array, index } => {
            expr_fallback_reason(array).or_else(|| expr_fallback_reason(index))
        }
        // Quantifiers — traverse body and triggers (#5406)
        ExprValue::Forall { body, triggers, .. } | ExprValue::Exists { body, triggers, .. } => {
            expr_fallback_reason(body)
                .or_else(|| triggers.iter().flatten().find_map(expr_fallback_reason))
        }
        // String/regex/seq, FP, and binary arithmetic — delegate to helpers
        _ => str_seq_re_fallback_reason(expr),
    }
}

/// Check string, regex, and sequence operations for fallback reasons.
///
/// All string/regex/seq operations are fully supported in direct execution
/// (#5969). This function traverses subexpressions to check for nested
/// fallback-requiring constructs (e.g., FP arithmetic inside a string predicate).
fn str_seq_re_fallback_reason(expr: &Expr) -> Option<String> {
    match expr.value() {
        // Unary string/regex/seq ops
        ExprValue::StrLen(inner)
        | ExprValue::StrToInt(inner)
        | ExprValue::StrFromInt(inner)
        | ExprValue::StrToRe(inner)
        | ExprValue::ReStar(inner)
        | ExprValue::RePlus(inner)
        | ExprValue::SeqUnit(inner)
        | ExprValue::SeqLen(inner) => expr_fallback_reason(inner),
        // Leaf: no subexpressions
        ExprValue::SeqEmpty(_) => None,
        // Binary string/regex/seq ops
        ExprValue::StrConcat(a, b)
        | ExprValue::StrAt(a, b)
        | ExprValue::StrContains(a, b)
        | ExprValue::StrPrefixOf(a, b)
        | ExprValue::StrSuffixOf(a, b)
        | ExprValue::StrInRe(a, b)
        | ExprValue::ReUnion(a, b)
        | ExprValue::ReConcat(a, b)
        | ExprValue::SeqConcat(a, b)
        | ExprValue::SeqNth(a, b)
        | ExprValue::SeqContains(a, b)
        | ExprValue::SeqPrefixOf(a, b)
        | ExprValue::SeqSuffixOf(a, b) => {
            expr_fallback_reason(a).or_else(|| expr_fallback_reason(b))
        }
        // Ternary string/seq ops
        ExprValue::StrSubstr(a, b, c)
        | ExprValue::StrIndexOf(a, b, c)
        | ExprValue::StrReplace(a, b, c)
        | ExprValue::StrReplaceAll(a, b, c)
        | ExprValue::SeqExtract(a, b, c)
        | ExprValue::SeqIndexOf(a, b, c)
        | ExprValue::SeqReplace(a, b, c) => expr_fallback_reason(a)
            .or_else(|| expr_fallback_reason(b))
            .or_else(|| expr_fallback_reason(c)),
        // Not a string/seq/regex op — delegate to FP and binary arithmetic
        _ => fp_or_binary_fallback_reason(expr),
    }
}

/// Check floating-point operations and binary ops for fallback reasons.
///
/// All FP operations are now fully implemented via bit-blasting and execute
/// directly (#5774, #6128). This function traverses subexpressions to check
/// for nested fallback-requiring constructs.
fn fp_or_binary_fallback_reason(expr: &Expr) -> Option<String> {
    match expr.value() {
        // FP arithmetic — fully bit-blasted (#6128), traverse subexpressions.
        ExprValue::FpAdd(_, a, b)
        | ExprValue::FpSub(_, a, b)
        | ExprValue::FpMul(_, a, b)
        | ExprValue::FpDiv(_, a, b) => expr_fallback_reason(a).or_else(|| expr_fallback_reason(b)),
        ExprValue::FpFma(_, a, b, c) => expr_fallback_reason(a)
            .or_else(|| expr_fallback_reason(b))
            .or_else(|| expr_fallback_reason(c)),
        ExprValue::FpSqrt(_, inner) | ExprValue::FpRoundToIntegral(_, inner) => {
            expr_fallback_reason(inner)
        }
        ExprValue::FpRem(a, b) => expr_fallback_reason(a).or_else(|| expr_fallback_reason(b)),
        // FP constants — leaf nodes, fully supported.
        ExprValue::FpPlusInfinity { .. }
        | ExprValue::FpMinusInfinity { .. }
        | ExprValue::FpNaN { .. }
        | ExprValue::FpPlusZero { .. }
        | ExprValue::FpMinusZero { .. } => None,
        // FP unary ops — fully bit-blasted, traverse subexpression.
        ExprValue::FpAbs(inner)
        | ExprValue::FpNeg(inner)
        | ExprValue::FpIsNaN(inner)
        | ExprValue::FpIsInfinite(inner)
        | ExprValue::FpIsZero(inner)
        | ExprValue::FpIsNormal(inner)
        | ExprValue::FpIsSubnormal(inner)
        | ExprValue::FpIsPositive(inner)
        | ExprValue::FpIsNegative(inner)
        | ExprValue::FpToReal(inner) => expr_fallback_reason(inner),
        // FP comparisons — fully bit-blasted, traverse subexpressions.
        ExprValue::FpEq(a, b)
        | ExprValue::FpLt(a, b)
        | ExprValue::FpLe(a, b)
        | ExprValue::FpGt(a, b)
        | ExprValue::FpGe(a, b) => expr_fallback_reason(a).or_else(|| expr_fallback_reason(b)),
        // FP min/max — fully implemented (minor signed-zero edge case per
        // #3586 but sound for all non-edge inputs), traverse subexpressions.
        ExprValue::FpMin(a, b) | ExprValue::FpMax(a, b) => {
            expr_fallback_reason(a).or_else(|| expr_fallback_reason(b))
        }
        // FP conversions — fully bit-blasted, traverse subexpressions.
        ExprValue::FpToSbv(_, inner, _)
        | ExprValue::FpToUbv(_, inner, _)
        | ExprValue::FpToFp(_, inner, _, _)
        | ExprValue::BvToFp(_, inner, _, _)
        | ExprValue::BvToFpUnsigned(_, inner, _, _) => expr_fallback_reason(inner),
        ExprValue::FpFromBvs(a, b, c) => expr_fallback_reason(a)
            .or_else(|| expr_fallback_reason(b))
            .or_else(|| expr_fallback_reason(c)),
        // Not an FP operation — delegate to binary arithmetic check.
        _ => binary_fallback_reason(expr),
    }
}

/// Check binary arithmetic, logic, and BV operations for fallback reasons.
fn binary_fallback_reason(expr: &Expr) -> Option<String> {
    match expr.value() {
        ExprValue::Xor(a, b)
        | ExprValue::Implies(a, b)
        | ExprValue::Eq(a, b)
        | ExprValue::IntAdd(a, b)
        | ExprValue::IntSub(a, b)
        | ExprValue::IntMul(a, b)
        | ExprValue::IntDiv(a, b)
        | ExprValue::IntMod(a, b)
        | ExprValue::IntLt(a, b)
        | ExprValue::IntLe(a, b)
        | ExprValue::IntGt(a, b)
        | ExprValue::IntGe(a, b)
        | ExprValue::RealAdd(a, b)
        | ExprValue::RealSub(a, b)
        | ExprValue::RealMul(a, b)
        | ExprValue::RealDiv(a, b)
        | ExprValue::RealLt(a, b)
        | ExprValue::RealLe(a, b)
        | ExprValue::RealGt(a, b)
        | ExprValue::RealGe(a, b)
        | ExprValue::BvAdd(a, b)
        | ExprValue::BvSub(a, b)
        | ExprValue::BvMul(a, b)
        | ExprValue::BvUDiv(a, b)
        | ExprValue::BvSDiv(a, b)
        | ExprValue::BvURem(a, b)
        | ExprValue::BvSRem(a, b)
        | ExprValue::BvAnd(a, b)
        | ExprValue::BvOr(a, b)
        | ExprValue::BvXor(a, b)
        | ExprValue::BvShl(a, b)
        | ExprValue::BvLShr(a, b)
        | ExprValue::BvAShr(a, b)
        | ExprValue::BvULt(a, b)
        | ExprValue::BvSLt(a, b)
        | ExprValue::BvULe(a, b)
        | ExprValue::BvUGt(a, b)
        | ExprValue::BvUGe(a, b)
        | ExprValue::BvSLe(a, b)
        | ExprValue::BvSGt(a, b)
        | ExprValue::BvSGe(a, b)
        | ExprValue::BvConcat(a, b)
        | ExprValue::BvAddNoOverflowUnsigned(a, b)
        | ExprValue::BvAddNoOverflowSigned(a, b)
        | ExprValue::BvSubNoUnderflowUnsigned(a, b)
        | ExprValue::BvSubNoOverflowSigned(a, b)
        | ExprValue::BvMulNoOverflowUnsigned(a, b)
        | ExprValue::BvMulNoOverflowSigned(a, b)
        | ExprValue::BvSdivNoOverflow(a, b) => {
            expr_fallback_reason(a).or_else(|| expr_fallback_reason(b))
        }
        _ => None,
    }
}
