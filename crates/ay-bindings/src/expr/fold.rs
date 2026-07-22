// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Expression fold (visitor) infrastructure for ay-bindings.
//!
//! Provides [`ExprFold`] trait and [`fold_expr`] driver so that consumers
//! (e.g. model-checker-consumer constant propagation) can traverse and transform expression
//! trees without manually enumerating ~120 [`ExprValue`] variants.
//!
//! ## Design
//!
//! The fold is a bottom-up rewrite: children are folded first, then the
//! parent is rebuilt with the new children via [`ExprFold::fold_post`].
//! Leaf nodes (constants, variables) get their own callbacks. Unknown
//! variants (from `#[non_exhaustive]` additions) go to `fold_unknown`.
//!
//! Part of #6170.

use super::{Expr, ExprValue};
use crate::sort::Sort;
use std::sync::Arc;

/// Red zone size for `stacker::maybe_grow` in expression fold recursion (#8414).
///
/// DT-heavy problems from verification-consumer can produce deeply nested expression trees
/// that overflow the default thread stack during fold traversal.
const FOLD_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for expression fold recursion.
const FOLD_STACK_SIZE: usize = 1024 * 1024;

/// Trait for bottom-up expression transformation.
///
/// Implement this trait to transform expression trees. The driver
/// [`fold_expr`] calls methods in bottom-up order:
///
/// 1. Recursively fold all children
/// 2. For variables → [`fold_var`](ExprFold::fold_var)
/// 3. For constants → [`fold_const`](ExprFold::fold_const)
/// 4. For compound expressions → [`fold_post`](ExprFold::fold_post)
/// 5. For unknown variants → [`fold_unknown`](ExprFold::fold_unknown)
///
/// Default implementations return the expression unchanged (identity fold).
pub trait ExprFold {
    /// Called for variable expressions (`ExprValue::Var`).
    ///
    /// Default: return the variable unchanged.
    fn fold_var(&mut self, name: &str, sort: &Sort) -> Expr {
        Expr::var(name.to_string(), sort.clone())
    }

    /// Called for constant (leaf) expressions: `BoolConst`, `BitVecConst`,
    /// `IntConst`, `RealConst`, `FpPlusInfinity`, `FpMinusInfinity`,
    /// `FpNaN`, `FpPlusZero`, `FpMinusZero`, `SeqEmpty`.
    ///
    /// Default: return the constant unchanged.
    fn fold_const(&mut self, expr: &Expr) -> Expr {
        expr.clone()
    }

    /// Called for compound expressions after all children have been folded.
    ///
    /// `original` is the pre-fold expression (for sort/metadata inspection).
    /// `children` contains the already-folded child expressions, in the same
    /// order as [`ExprValue::children`] returns them.
    ///
    /// Default: rebuild the expression with the new children.
    fn fold_post(&mut self, original: &Expr, children: Vec<Expr>) -> Expr {
        rebuild_with_children(original, children)
    }

    /// Called for variants not recognized by the fold driver.
    ///
    /// This handles variants added after the fold was compiled, due to
    /// `#[non_exhaustive]` on [`ExprValue`]. Consumers that need to abort
    /// on unrecognized variants should check [`ExprValue::is_known_variant`]
    /// or override this to return an error/panic.
    ///
    /// Default: return the expression unchanged.
    fn fold_unknown(&mut self, expr: &Expr) -> Expr {
        expr.clone()
    }
}

/// Drive a bottom-up fold over an expression tree.
///
/// Recursively folds children first, then dispatches to the appropriate
/// [`ExprFold`] method for the current node.
///
/// Uses `stacker::maybe_grow` for stack safety on deeply nested expressions (#8414).
pub fn fold_expr<F: ExprFold>(folder: &mut F, expr: &Expr) -> Expr {
    stacker::maybe_grow(FOLD_STACK_RED_ZONE, FOLD_STACK_SIZE, || {
        match expr.value() {
            ExprValue::Var { ref name } => folder.fold_var(name, expr.sort()),

            // Constants (0 children, known leaf)
            ExprValue::BoolConst(_)
            | ExprValue::BitVecConst { .. }
            | ExprValue::IntConst(_)
            | ExprValue::RealConst(_)
            | ExprValue::FpPlusInfinity { .. }
            | ExprValue::FpMinusInfinity { .. }
            | ExprValue::FpNaN { .. }
            | ExprValue::FpPlusZero { .. }
            | ExprValue::FpMinusZero { .. }
            | ExprValue::SeqEmpty(_) => folder.fold_const(expr),

            // Compound expressions: fold children first, then fold_post
            _ if expr.value().is_known_variant() => {
                let children: Vec<Expr> = expr
                    .value()
                    .children()
                    .map(|child| fold_expr(folder, child))
                    .collect();
                folder.fold_post(expr, children)
            }

            // Unknown variant from #[non_exhaustive] extension
            _ => folder.fold_unknown(expr),
        }
    }) // stacker::maybe_grow
}

/// Rebuild an expression with new children, preserving the variant and sort.
///
/// This is the default implementation for [`ExprFold::fold_post`]. It
/// reconstructs the same `ExprValue` variant with the provided children
/// substituted in order.
///
/// # Panics
///
/// Panics if `children.len()` does not match the expected child count for
/// the variant.
#[must_use]
pub fn rebuild_with_children(original: &Expr, children: Vec<Expr>) -> Expr {
    let sort = original.sort().clone();
    let mut it = children.into_iter();

    let value = match original.value() {
        // Constants and Var — should not reach here via fold_post, but handle gracefully
        ExprValue::BoolConst(_)
        | ExprValue::BitVecConst { .. }
        | ExprValue::IntConst(_)
        | ExprValue::RealConst(_)
        | ExprValue::Var { .. }
        | ExprValue::FpPlusInfinity { .. }
        | ExprValue::FpMinusInfinity { .. }
        | ExprValue::FpNaN { .. }
        | ExprValue::FpPlusZero { .. }
        | ExprValue::FpMinusZero { .. }
        | ExprValue::SeqEmpty(_) => {
            return original.clone();
        }

        // ===== Unary =====
        ExprValue::Not(_) => ExprValue::Not(it.next().unwrap()),
        ExprValue::BvNeg(_) => ExprValue::BvNeg(it.next().unwrap()),
        ExprValue::BvNot(_) => ExprValue::BvNot(it.next().unwrap()),
        ExprValue::IntNeg(_) => ExprValue::IntNeg(it.next().unwrap()),
        ExprValue::IntToReal(_) => ExprValue::IntToReal(it.next().unwrap()),
        ExprValue::RealToInt(_) => ExprValue::RealToInt(it.next().unwrap()),
        ExprValue::IsInt(_) => ExprValue::IsInt(it.next().unwrap()),
        ExprValue::RealNeg(_) => ExprValue::RealNeg(it.next().unwrap()),
        ExprValue::Bv2Int(_) => ExprValue::Bv2Int(it.next().unwrap()),
        ExprValue::FpAbs(_) => ExprValue::FpAbs(it.next().unwrap()),
        ExprValue::FpNeg(_) => ExprValue::FpNeg(it.next().unwrap()),
        ExprValue::FpIsNaN(_) => ExprValue::FpIsNaN(it.next().unwrap()),
        ExprValue::FpIsInfinite(_) => ExprValue::FpIsInfinite(it.next().unwrap()),
        ExprValue::FpIsZero(_) => ExprValue::FpIsZero(it.next().unwrap()),
        ExprValue::FpIsNormal(_) => ExprValue::FpIsNormal(it.next().unwrap()),
        ExprValue::FpIsSubnormal(_) => ExprValue::FpIsSubnormal(it.next().unwrap()),
        ExprValue::FpIsPositive(_) => ExprValue::FpIsPositive(it.next().unwrap()),
        ExprValue::FpIsNegative(_) => ExprValue::FpIsNegative(it.next().unwrap()),
        ExprValue::FpToReal(_) => ExprValue::FpToReal(it.next().unwrap()),
        ExprValue::FpToIeeeBv(_) => ExprValue::FpToIeeeBv(it.next().unwrap()),
        ExprValue::BvNegNoOverflow(_) => ExprValue::BvNegNoOverflow(it.next().unwrap()),
        ExprValue::StrLen(_) => ExprValue::StrLen(it.next().unwrap()),
        ExprValue::StrToInt(_) => ExprValue::StrToInt(it.next().unwrap()),
        ExprValue::StrFromInt(_) => ExprValue::StrFromInt(it.next().unwrap()),
        ExprValue::StrToRe(_) => ExprValue::StrToRe(it.next().unwrap()),
        ExprValue::ReStar(_) => ExprValue::ReStar(it.next().unwrap()),
        ExprValue::RePlus(_) => ExprValue::RePlus(it.next().unwrap()),
        ExprValue::SeqUnit(_) => ExprValue::SeqUnit(it.next().unwrap()),
        ExprValue::SeqLen(_) => ExprValue::SeqLen(it.next().unwrap()),

        // ===== Unary with extra data =====
        ExprValue::BvZeroExtend { extra_bits, .. } => ExprValue::BvZeroExtend {
            expr: it.next().unwrap(),
            extra_bits: *extra_bits,
        },
        ExprValue::BvSignExtend { extra_bits, .. } => ExprValue::BvSignExtend {
            expr: it.next().unwrap(),
            extra_bits: *extra_bits,
        },
        ExprValue::BvExtract { high, low, .. } => ExprValue::BvExtract {
            expr: it.next().unwrap(),
            high: *high,
            low: *low,
        },
        ExprValue::Int2Bv(_, width) => ExprValue::Int2Bv(it.next().unwrap(), *width),
        ExprValue::FpSqrt(rm, _) => ExprValue::FpSqrt(*rm, it.next().unwrap()),
        ExprValue::FpRoundToIntegral(rm, _) => {
            ExprValue::FpRoundToIntegral(*rm, it.next().unwrap())
        }
        ExprValue::FpToSbv(rm, _, w) => ExprValue::FpToSbv(*rm, it.next().unwrap(), *w),
        ExprValue::FpToUbv(rm, _, w) => ExprValue::FpToUbv(*rm, it.next().unwrap(), *w),
        ExprValue::BvToFp(rm, _, eb, sb) => ExprValue::BvToFp(*rm, it.next().unwrap(), *eb, *sb),
        ExprValue::BvToFpUnsigned(rm, _, eb, sb) => {
            ExprValue::BvToFpUnsigned(*rm, it.next().unwrap(), *eb, *sb)
        }
        ExprValue::FpToFp(rm, _, eb, sb) => ExprValue::FpToFp(*rm, it.next().unwrap(), *eb, *sb),
        ExprValue::ConstArray { index_sort, .. } => ExprValue::ConstArray {
            index_sort: index_sort.clone(),
            value: it.next().unwrap(),
        },
        ExprValue::DatatypeSelector {
            datatype_name,
            selector_name,
            ..
        } => ExprValue::DatatypeSelector {
            datatype_name: datatype_name.clone(),
            selector_name: selector_name.clone(),
            expr: it.next().unwrap(),
        },
        ExprValue::DatatypeTester {
            datatype_name,
            constructor_name,
            ..
        } => ExprValue::DatatypeTester {
            datatype_name: datatype_name.clone(),
            constructor_name: constructor_name.clone(),
            expr: it.next().unwrap(),
        },

        // ===== Binary =====
        ExprValue::Xor(_, _) => {
            let a = it.next().unwrap();
            ExprValue::Xor(a, it.next().unwrap())
        }
        ExprValue::Implies(_, _) => {
            let a = it.next().unwrap();
            ExprValue::Implies(a, it.next().unwrap())
        }
        ExprValue::Eq(_, _) => {
            let a = it.next().unwrap();
            ExprValue::Eq(a, it.next().unwrap())
        }
        ExprValue::BvAdd(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvAdd(a, it.next().unwrap())
        }
        ExprValue::BvSub(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvSub(a, it.next().unwrap())
        }
        ExprValue::BvMul(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvMul(a, it.next().unwrap())
        }
        ExprValue::BvUDiv(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvUDiv(a, it.next().unwrap())
        }
        ExprValue::BvSDiv(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvSDiv(a, it.next().unwrap())
        }
        ExprValue::BvURem(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvURem(a, it.next().unwrap())
        }
        ExprValue::BvSRem(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvSRem(a, it.next().unwrap())
        }
        ExprValue::BvAnd(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvAnd(a, it.next().unwrap())
        }
        ExprValue::BvOr(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvOr(a, it.next().unwrap())
        }
        ExprValue::BvXor(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvXor(a, it.next().unwrap())
        }
        ExprValue::BvShl(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvShl(a, it.next().unwrap())
        }
        ExprValue::BvLShr(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvLShr(a, it.next().unwrap())
        }
        ExprValue::BvAShr(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvAShr(a, it.next().unwrap())
        }
        ExprValue::BvULt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvULt(a, it.next().unwrap())
        }
        ExprValue::BvULe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvULe(a, it.next().unwrap())
        }
        ExprValue::BvUGt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvUGt(a, it.next().unwrap())
        }
        ExprValue::BvUGe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvUGe(a, it.next().unwrap())
        }
        ExprValue::BvSLt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvSLt(a, it.next().unwrap())
        }
        ExprValue::BvSLe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvSLe(a, it.next().unwrap())
        }
        ExprValue::BvSGt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvSGt(a, it.next().unwrap())
        }
        ExprValue::BvSGe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvSGe(a, it.next().unwrap())
        }
        ExprValue::BvConcat(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvConcat(a, it.next().unwrap())
        }
        ExprValue::BvAddNoOverflowUnsigned(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvAddNoOverflowUnsigned(a, it.next().unwrap())
        }
        ExprValue::BvAddNoOverflowSigned(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvAddNoOverflowSigned(a, it.next().unwrap())
        }
        ExprValue::BvSubNoUnderflowUnsigned(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvSubNoUnderflowUnsigned(a, it.next().unwrap())
        }
        ExprValue::BvSubNoOverflowSigned(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvSubNoOverflowSigned(a, it.next().unwrap())
        }
        ExprValue::BvMulNoOverflowUnsigned(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvMulNoOverflowUnsigned(a, it.next().unwrap())
        }
        ExprValue::BvMulNoOverflowSigned(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvMulNoOverflowSigned(a, it.next().unwrap())
        }
        ExprValue::BvSdivNoOverflow(_, _) => {
            let a = it.next().unwrap();
            ExprValue::BvSdivNoOverflow(a, it.next().unwrap())
        }
        ExprValue::IntAdd(_, _) => {
            let a = it.next().unwrap();
            ExprValue::IntAdd(a, it.next().unwrap())
        }
        ExprValue::IntSub(_, _) => {
            let a = it.next().unwrap();
            ExprValue::IntSub(a, it.next().unwrap())
        }
        ExprValue::IntMul(_, _) => {
            let a = it.next().unwrap();
            ExprValue::IntMul(a, it.next().unwrap())
        }
        ExprValue::IntDiv(_, _) => {
            let a = it.next().unwrap();
            ExprValue::IntDiv(a, it.next().unwrap())
        }
        ExprValue::IntMod(_, _) => {
            let a = it.next().unwrap();
            ExprValue::IntMod(a, it.next().unwrap())
        }
        ExprValue::IntLt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::IntLt(a, it.next().unwrap())
        }
        ExprValue::IntLe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::IntLe(a, it.next().unwrap())
        }
        ExprValue::IntGt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::IntGt(a, it.next().unwrap())
        }
        ExprValue::IntGe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::IntGe(a, it.next().unwrap())
        }
        ExprValue::RealAdd(_, _) => {
            let a = it.next().unwrap();
            ExprValue::RealAdd(a, it.next().unwrap())
        }
        ExprValue::RealSub(_, _) => {
            let a = it.next().unwrap();
            ExprValue::RealSub(a, it.next().unwrap())
        }
        ExprValue::RealMul(_, _) => {
            let a = it.next().unwrap();
            ExprValue::RealMul(a, it.next().unwrap())
        }
        ExprValue::RealDiv(_, _) => {
            let a = it.next().unwrap();
            ExprValue::RealDiv(a, it.next().unwrap())
        }
        ExprValue::RealLt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::RealLt(a, it.next().unwrap())
        }
        ExprValue::RealLe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::RealLe(a, it.next().unwrap())
        }
        ExprValue::RealGt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::RealGt(a, it.next().unwrap())
        }
        ExprValue::RealGe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::RealGe(a, it.next().unwrap())
        }
        ExprValue::Select { .. } => {
            let array = it.next().unwrap();
            ExprValue::Select {
                array,
                index: it.next().unwrap(),
            }
        }
        ExprValue::StrConcat(_, _) => {
            let a = it.next().unwrap();
            ExprValue::StrConcat(a, it.next().unwrap())
        }
        ExprValue::StrAt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::StrAt(a, it.next().unwrap())
        }
        ExprValue::StrContains(_, _) => {
            let a = it.next().unwrap();
            ExprValue::StrContains(a, it.next().unwrap())
        }
        ExprValue::StrPrefixOf(_, _) => {
            let a = it.next().unwrap();
            ExprValue::StrPrefixOf(a, it.next().unwrap())
        }
        ExprValue::StrSuffixOf(_, _) => {
            let a = it.next().unwrap();
            ExprValue::StrSuffixOf(a, it.next().unwrap())
        }
        ExprValue::StrInRe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::StrInRe(a, it.next().unwrap())
        }
        ExprValue::ReUnion(_, _) => {
            let a = it.next().unwrap();
            ExprValue::ReUnion(a, it.next().unwrap())
        }
        ExprValue::ReConcat(_, _) => {
            let a = it.next().unwrap();
            ExprValue::ReConcat(a, it.next().unwrap())
        }
        ExprValue::SeqConcat(_, _) => {
            let a = it.next().unwrap();
            ExprValue::SeqConcat(a, it.next().unwrap())
        }
        ExprValue::SeqNth(_, _) => {
            let a = it.next().unwrap();
            ExprValue::SeqNth(a, it.next().unwrap())
        }
        ExprValue::SeqContains(_, _) => {
            let a = it.next().unwrap();
            ExprValue::SeqContains(a, it.next().unwrap())
        }
        ExprValue::SeqPrefixOf(_, _) => {
            let a = it.next().unwrap();
            ExprValue::SeqPrefixOf(a, it.next().unwrap())
        }
        ExprValue::SeqSuffixOf(_, _) => {
            let a = it.next().unwrap();
            ExprValue::SeqSuffixOf(a, it.next().unwrap())
        }
        ExprValue::FpEq(_, _) => {
            let a = it.next().unwrap();
            ExprValue::FpEq(a, it.next().unwrap())
        }
        ExprValue::FpLt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::FpLt(a, it.next().unwrap())
        }
        ExprValue::FpLe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::FpLe(a, it.next().unwrap())
        }
        ExprValue::FpGt(_, _) => {
            let a = it.next().unwrap();
            ExprValue::FpGt(a, it.next().unwrap())
        }
        ExprValue::FpGe(_, _) => {
            let a = it.next().unwrap();
            ExprValue::FpGe(a, it.next().unwrap())
        }
        ExprValue::FpRem(_, _) => {
            let a = it.next().unwrap();
            ExprValue::FpRem(a, it.next().unwrap())
        }
        ExprValue::FpMin(_, _) => {
            let a = it.next().unwrap();
            ExprValue::FpMin(a, it.next().unwrap())
        }
        ExprValue::FpMax(_, _) => {
            let a = it.next().unwrap();
            ExprValue::FpMax(a, it.next().unwrap())
        }

        // ===== Binary with rounding mode =====
        ExprValue::FpAdd(rm, _, _) => {
            let a = it.next().unwrap();
            ExprValue::FpAdd(*rm, a, it.next().unwrap())
        }
        ExprValue::FpSub(rm, _, _) => {
            let a = it.next().unwrap();
            ExprValue::FpSub(*rm, a, it.next().unwrap())
        }
        ExprValue::FpMul(rm, _, _) => {
            let a = it.next().unwrap();
            ExprValue::FpMul(*rm, a, it.next().unwrap())
        }
        ExprValue::FpDiv(rm, _, _) => {
            let a = it.next().unwrap();
            ExprValue::FpDiv(*rm, a, it.next().unwrap())
        }

        // ===== Ternary =====
        ExprValue::Ite { .. } => {
            let cond = it.next().unwrap();
            let then_expr = it.next().unwrap();
            ExprValue::Ite {
                cond,
                then_expr,
                else_expr: it.next().unwrap(),
            }
        }
        ExprValue::Store { .. } => {
            let array = it.next().unwrap();
            let index = it.next().unwrap();
            ExprValue::Store {
                array,
                index,
                value: it.next().unwrap(),
            }
        }
        ExprValue::StrSubstr(_, _, _) => {
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            ExprValue::StrSubstr(a, b, it.next().unwrap())
        }
        ExprValue::StrIndexOf(_, _, _) => {
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            ExprValue::StrIndexOf(a, b, it.next().unwrap())
        }
        ExprValue::StrReplace(_, _, _) => {
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            ExprValue::StrReplace(a, b, it.next().unwrap())
        }
        ExprValue::StrReplaceAll(_, _, _) => {
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            ExprValue::StrReplaceAll(a, b, it.next().unwrap())
        }
        ExprValue::SeqExtract(_, _, _) => {
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            ExprValue::SeqExtract(a, b, it.next().unwrap())
        }
        ExprValue::SeqIndexOf(_, _, _) => {
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            ExprValue::SeqIndexOf(a, b, it.next().unwrap())
        }
        ExprValue::SeqReplace(_, _, _) => {
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            ExprValue::SeqReplace(a, b, it.next().unwrap())
        }
        ExprValue::FpFromBvs(_, _, _) => {
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            ExprValue::FpFromBvs(a, b, it.next().unwrap())
        }

        // ===== Ternary with rounding mode =====
        ExprValue::FpFma(rm, _, _, _) => {
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            ExprValue::FpFma(*rm, a, b, it.next().unwrap())
        }

        // ===== N-ary =====
        ExprValue::And(_) => ExprValue::And(it.collect()),
        ExprValue::Or(_) => ExprValue::Or(it.collect()),
        ExprValue::Distinct(_) => ExprValue::Distinct(it.collect()),

        // ===== Quantifiers — children are body + trigger exprs =====
        ExprValue::Forall { vars, triggers, .. } => {
            let new_body = it.next().unwrap();
            let new_triggers = rebuild_triggers(triggers, &mut it);
            ExprValue::Forall {
                vars: vars.clone(),
                body: new_body,
                triggers: new_triggers,
            }
        }
        ExprValue::Exists { vars, triggers, .. } => {
            let new_body = it.next().unwrap();
            let new_triggers = rebuild_triggers(triggers, &mut it);
            ExprValue::Exists {
                vars: vars.clone(),
                body: new_body,
                triggers: new_triggers,
            }
        }

        // ===== Datatype constructor and FuncApp (variable arity) =====
        ExprValue::DatatypeConstructor {
            datatype_name,
            constructor_name,
            ..
        } => ExprValue::DatatypeConstructor {
            datatype_name: datatype_name.clone(),
            constructor_name: constructor_name.clone(),
            args: it.collect(),
        },
        ExprValue::FuncApp { name, .. } => ExprValue::FuncApp {
            name: name.clone(),
            args: it.collect(),
        },

        // Unknown variant — should not reach here
        #[allow(unreachable_patterns)]
        _ => return original.clone(),
    };

    Expr {
        sort,
        value: Arc::new(value),
    }
}

/// Rebuild trigger groups from a flat iterator of folded expressions.
///
/// Triggers are stored as `Vec<Vec<Expr>>` — groups of pattern terms.
/// We flatten them for folding and reconstruct the group structure here.
fn rebuild_triggers(
    original_triggers: &[Vec<Expr>],
    it: &mut impl Iterator<Item = Expr>,
) -> Vec<Vec<Expr>> {
    original_triggers
        .iter()
        .map(|group| {
            group
                .iter()
                .map(|_| it.next().expect("trigger expression count mismatch"))
                .collect()
        })
        .collect()
}

#[cfg(test)]
#[path = "fold_tests.rs"]
mod tests;
