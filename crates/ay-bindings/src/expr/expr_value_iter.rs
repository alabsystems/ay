// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ExprValue traversal methods: `children()` and `is_known_variant()`.
//!
//! Extracted from `expr_value.rs` for code health (#5970).

use super::{Expr, ExprValue};

#[allow(clippy::use_self)] // ExprValue:: is clearer than Self:: for 120+ variant enums
impl ExprValue {
    /// Returns an iterator over the child expressions of this node.
    ///
    /// Leaf nodes (constants, variables) return an empty iterator.
    /// Compound nodes return children in a deterministic order matching
    /// the field order in the enum variant.
    ///
    /// This is the **single enumeration point** for `ExprValue` variants.
    /// When new variants are added, only this method (and `is_known_variant`)
    /// need updating.
    ///
    /// Part of #6170.
    pub fn children(&self) -> impl Iterator<Item = &Expr> {
        // We collect into a small Vec to allow returning a uniform iterator
        // type. The vast majority of nodes have 0-3 children.
        let refs: Vec<&Expr> = match self {
            // ===== Leaves: 0 children =====
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
            | ExprValue::SeqEmpty(_) => vec![],

            // ===== Unary: 1 child =====
            ExprValue::Not(a)
            | ExprValue::BvNeg(a)
            | ExprValue::BvNot(a)
            | ExprValue::IntNeg(a)
            | ExprValue::IntToReal(a)
            | ExprValue::RealToInt(a)
            | ExprValue::IsInt(a)
            | ExprValue::RealNeg(a)
            | ExprValue::Bv2Int(a)
            | ExprValue::FpAbs(a)
            | ExprValue::FpNeg(a)
            | ExprValue::FpIsNaN(a)
            | ExprValue::FpIsInfinite(a)
            | ExprValue::FpIsZero(a)
            | ExprValue::FpIsNormal(a)
            | ExprValue::FpIsSubnormal(a)
            | ExprValue::FpIsPositive(a)
            | ExprValue::FpIsNegative(a)
            | ExprValue::FpToReal(a)
            | ExprValue::FpToIeeeBv(a)
            | ExprValue::BvNegNoOverflow(a)
            | ExprValue::StrLen(a)
            | ExprValue::StrToInt(a)
            | ExprValue::StrFromInt(a)
            | ExprValue::StrToRe(a)
            | ExprValue::ReStar(a)
            | ExprValue::RePlus(a)
            | ExprValue::SeqUnit(a)
            | ExprValue::SeqLen(a) => vec![a],

            // Unary with extra non-Expr fields
            ExprValue::BvZeroExtend { expr, .. }
            | ExprValue::BvSignExtend { expr, .. }
            | ExprValue::BvExtract { expr, .. }
            | ExprValue::DatatypeSelector { expr, .. }
            | ExprValue::DatatypeTester { expr, .. } => vec![expr],
            ExprValue::Int2Bv(a, _)
            | ExprValue::FpSqrt(_, a)
            | ExprValue::FpRoundToIntegral(_, a)
            | ExprValue::FpToSbv(_, a, _)
            | ExprValue::FpToUbv(_, a, _)
            | ExprValue::BvToFp(_, a, _, _)
            | ExprValue::BvToFpUnsigned(_, a, _, _)
            | ExprValue::FpToFp(_, a, _, _) => vec![a],
            ExprValue::ConstArray { value, .. } => vec![value],

            // ===== Binary: 2 children =====
            ExprValue::Xor(a, b)
            | ExprValue::Implies(a, b)
            | ExprValue::Eq(a, b)
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
            | ExprValue::BvULe(a, b)
            | ExprValue::BvUGt(a, b)
            | ExprValue::BvUGe(a, b)
            | ExprValue::BvSLt(a, b)
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
            | ExprValue::BvSdivNoOverflow(a, b)
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
            | ExprValue::StrConcat(a, b)
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
            | ExprValue::SeqSuffixOf(a, b)
            | ExprValue::FpEq(a, b)
            | ExprValue::FpLt(a, b)
            | ExprValue::FpLe(a, b)
            | ExprValue::FpGt(a, b)
            | ExprValue::FpGe(a, b)
            | ExprValue::FpRem(a, b)
            | ExprValue::FpMin(a, b)
            | ExprValue::FpMax(a, b) => vec![a, b],

            ExprValue::Select { array, index } => vec![array, index],

            // Binary with rounding mode (rm is not an Expr)
            ExprValue::FpAdd(_, a, b)
            | ExprValue::FpSub(_, a, b)
            | ExprValue::FpMul(_, a, b)
            | ExprValue::FpDiv(_, a, b) => vec![a, b],

            // ===== Ternary: 3 children =====
            ExprValue::Ite {
                cond,
                then_expr,
                else_expr,
            } => vec![cond, then_expr, else_expr],
            ExprValue::Store {
                array,
                index,
                value,
            } => vec![array, index, value],
            ExprValue::StrSubstr(a, b, c)
            | ExprValue::StrIndexOf(a, b, c)
            | ExprValue::StrReplace(a, b, c)
            | ExprValue::StrReplaceAll(a, b, c)
            | ExprValue::SeqExtract(a, b, c)
            | ExprValue::SeqIndexOf(a, b, c)
            | ExprValue::SeqReplace(a, b, c)
            | ExprValue::FpFromBvs(a, b, c) => vec![a, b, c],

            // Ternary with rounding mode
            ExprValue::FpFma(_, a, b, c) => vec![a, b, c],

            // ===== N-ary =====
            ExprValue::And(exprs) | ExprValue::Or(exprs) | ExprValue::Distinct(exprs) => {
                exprs.iter().collect()
            }

            // Quantifiers: body + all trigger expressions
            ExprValue::Forall { body, triggers, .. } | ExprValue::Exists { body, triggers, .. } => {
                let mut refs = vec![body];
                for group in triggers {
                    refs.extend(group.iter());
                }
                refs
            }

            // Variable-arity
            ExprValue::DatatypeConstructor { args, .. } | ExprValue::FuncApp { args, .. } => {
                args.iter().collect()
            }

            // Unknown variant from #[non_exhaustive]
            #[allow(unreachable_patterns)]
            _ => vec![],
        };
        refs.into_iter()
    }

    /// Consumes self and returns owned child expressions in a Vec.
    ///
    /// This is the owning counterpart to [`children`]. Used by the iterative
    /// `Drop` implementation to extract children without recursion (#8414).
    ///
    /// Leaf nodes return an empty Vec. Compound nodes return children in the
    /// same order as [`children`].
    #[allow(clippy::use_self)]
    pub(crate) fn into_children_vec(self) -> Vec<Expr> {
        match self {
            // ===== Leaves: 0 children =====
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
            | ExprValue::SeqEmpty(_) => vec![],

            // ===== Unary: 1 child =====
            ExprValue::Not(a)
            | ExprValue::BvNeg(a)
            | ExprValue::BvNot(a)
            | ExprValue::IntNeg(a)
            | ExprValue::IntToReal(a)
            | ExprValue::RealToInt(a)
            | ExprValue::IsInt(a)
            | ExprValue::RealNeg(a)
            | ExprValue::Bv2Int(a)
            | ExprValue::FpAbs(a)
            | ExprValue::FpNeg(a)
            | ExprValue::FpIsNaN(a)
            | ExprValue::FpIsInfinite(a)
            | ExprValue::FpIsZero(a)
            | ExprValue::FpIsNormal(a)
            | ExprValue::FpIsSubnormal(a)
            | ExprValue::FpIsPositive(a)
            | ExprValue::FpIsNegative(a)
            | ExprValue::FpToReal(a)
            | ExprValue::FpToIeeeBv(a)
            | ExprValue::BvNegNoOverflow(a)
            | ExprValue::StrLen(a)
            | ExprValue::StrToInt(a)
            | ExprValue::StrFromInt(a)
            | ExprValue::StrToRe(a)
            | ExprValue::ReStar(a)
            | ExprValue::RePlus(a)
            | ExprValue::SeqUnit(a)
            | ExprValue::SeqLen(a) => vec![a],

            // Unary with extra non-Expr fields
            ExprValue::BvZeroExtend { expr, .. }
            | ExprValue::BvSignExtend { expr, .. }
            | ExprValue::BvExtract { expr, .. }
            | ExprValue::DatatypeSelector { expr, .. }
            | ExprValue::DatatypeTester { expr, .. } => vec![expr],
            ExprValue::Int2Bv(a, _)
            | ExprValue::FpSqrt(_, a)
            | ExprValue::FpRoundToIntegral(_, a)
            | ExprValue::FpToSbv(_, a, _)
            | ExprValue::FpToUbv(_, a, _)
            | ExprValue::BvToFp(_, a, _, _)
            | ExprValue::BvToFpUnsigned(_, a, _, _)
            | ExprValue::FpToFp(_, a, _, _) => vec![a],
            ExprValue::ConstArray { value, .. } => vec![value],

            // ===== Binary: 2 children =====
            ExprValue::Xor(a, b)
            | ExprValue::Implies(a, b)
            | ExprValue::Eq(a, b)
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
            | ExprValue::BvULe(a, b)
            | ExprValue::BvUGt(a, b)
            | ExprValue::BvUGe(a, b)
            | ExprValue::BvSLt(a, b)
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
            | ExprValue::BvSdivNoOverflow(a, b)
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
            | ExprValue::StrConcat(a, b)
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
            | ExprValue::SeqSuffixOf(a, b)
            | ExprValue::FpEq(a, b)
            | ExprValue::FpLt(a, b)
            | ExprValue::FpLe(a, b)
            | ExprValue::FpGt(a, b)
            | ExprValue::FpGe(a, b)
            | ExprValue::FpRem(a, b)
            | ExprValue::FpMin(a, b)
            | ExprValue::FpMax(a, b) => vec![a, b],

            ExprValue::Select { array, index } => vec![array, index],

            // Binary with rounding mode (rm is not an Expr)
            ExprValue::FpAdd(_, a, b)
            | ExprValue::FpSub(_, a, b)
            | ExprValue::FpMul(_, a, b)
            | ExprValue::FpDiv(_, a, b) => vec![a, b],

            // ===== Ternary: 3 children =====
            ExprValue::Ite {
                cond,
                then_expr,
                else_expr,
            } => vec![cond, then_expr, else_expr],
            ExprValue::Store {
                array,
                index,
                value,
            } => vec![array, index, value],
            ExprValue::StrSubstr(a, b, c)
            | ExprValue::StrIndexOf(a, b, c)
            | ExprValue::StrReplace(a, b, c)
            | ExprValue::StrReplaceAll(a, b, c)
            | ExprValue::SeqExtract(a, b, c)
            | ExprValue::SeqIndexOf(a, b, c)
            | ExprValue::SeqReplace(a, b, c)
            | ExprValue::FpFromBvs(a, b, c) => vec![a, b, c],

            // Ternary with rounding mode
            ExprValue::FpFma(_, a, b, c) => vec![a, b, c],

            // ===== N-ary =====
            ExprValue::And(exprs) | ExprValue::Or(exprs) | ExprValue::Distinct(exprs) => exprs,

            // Quantifiers: body + all trigger expressions
            ExprValue::Forall {
                body,
                triggers,
                vars: _,
            }
            | ExprValue::Exists {
                body,
                triggers,
                vars: _,
            } => {
                let mut children = vec![body];
                for group in triggers {
                    children.extend(group);
                }
                children
            }

            // Variable-arity
            ExprValue::DatatypeConstructor { args, .. } | ExprValue::FuncApp { args, .. } => args,

            // Unknown variant from #[non_exhaustive]
            #[allow(unreachable_patterns)]
            _ => vec![],
        }
    }

    /// Returns `true` if this variant is recognized by the current
    /// version of ay-bindings.
    ///
    /// This distinguishes "known leaf with 0 children" (e.g., `BoolConst`)
    /// from "unknown variant with 0 children" (a variant added after this
    /// code was compiled, due to `#[non_exhaustive]`).
    ///
    /// Consumers that need conservative behavior on unrecognized variants
    /// (e.g., abort rather than silently skip) should check this method.
    ///
    /// Part of #6170.
    #[must_use]
    pub fn is_known_variant(&self) -> bool {
        // Exhaustive match on all known variants. The wildcard at the end
        // catches any variants added after compilation.
        #[deny(unreachable_patterns)]
        match self {
            ExprValue::BoolConst(_)
            | ExprValue::BitVecConst { .. }
            | ExprValue::IntConst(_)
            | ExprValue::RealConst(_)
            | ExprValue::Var { .. }
            | ExprValue::Not(_)
            | ExprValue::And(_)
            | ExprValue::Or(_)
            | ExprValue::Xor(_, _)
            | ExprValue::Implies(_, _)
            | ExprValue::Ite { .. }
            | ExprValue::Eq(_, _)
            | ExprValue::Distinct(_)
            | ExprValue::BvAdd(_, _)
            | ExprValue::BvSub(_, _)
            | ExprValue::BvMul(_, _)
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
            | ExprValue::BvULt(_, _)
            | ExprValue::BvULe(_, _)
            | ExprValue::BvUGt(_, _)
            | ExprValue::BvUGe(_, _)
            | ExprValue::BvSLt(_, _)
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
            | ExprValue::IntToReal(_)
            | ExprValue::RealToInt(_)
            | ExprValue::IsInt(_)
            | ExprValue::RealAdd(_, _)
            | ExprValue::RealSub(_, _)
            | ExprValue::RealMul(_, _)
            | ExprValue::RealDiv(_, _)
            | ExprValue::RealNeg(_)
            | ExprValue::RealLt(_, _)
            | ExprValue::RealLe(_, _)
            | ExprValue::RealGt(_, _)
            | ExprValue::RealGe(_, _)
            | ExprValue::Select { .. }
            | ExprValue::Store { .. }
            | ExprValue::ConstArray { .. }
            | ExprValue::DatatypeConstructor { .. }
            | ExprValue::DatatypeSelector { .. }
            | ExprValue::DatatypeTester { .. }
            | ExprValue::FpPlusInfinity { .. }
            | ExprValue::FpMinusInfinity { .. }
            | ExprValue::FpNaN { .. }
            | ExprValue::FpPlusZero { .. }
            | ExprValue::FpMinusZero { .. }
            | ExprValue::FpAbs(_)
            | ExprValue::FpNeg(_)
            | ExprValue::FpAdd(_, _, _)
            | ExprValue::FpSub(_, _, _)
            | ExprValue::FpMul(_, _, _)
            | ExprValue::FpDiv(_, _, _)
            | ExprValue::FpFma(_, _, _, _)
            | ExprValue::FpSqrt(_, _)
            | ExprValue::FpRem(_, _)
            | ExprValue::FpRoundToIntegral(_, _)
            | ExprValue::FpMin(_, _)
            | ExprValue::FpMax(_, _)
            | ExprValue::FpEq(_, _)
            | ExprValue::FpLt(_, _)
            | ExprValue::FpLe(_, _)
            | ExprValue::FpGt(_, _)
            | ExprValue::FpGe(_, _)
            | ExprValue::FpIsNaN(_)
            | ExprValue::FpIsInfinite(_)
            | ExprValue::FpIsZero(_)
            | ExprValue::FpIsNormal(_)
            | ExprValue::FpIsSubnormal(_)
            | ExprValue::FpIsPositive(_)
            | ExprValue::FpIsNegative(_)
            | ExprValue::FpToSbv(_, _, _)
            | ExprValue::FpToUbv(_, _, _)
            | ExprValue::FpToReal(_)
            | ExprValue::FpFromBvs(_, _, _)
            | ExprValue::BvToFp(_, _, _, _)
            | ExprValue::BvToFpUnsigned(_, _, _, _)
            | ExprValue::FpToFp(_, _, _, _)
            | ExprValue::FpToIeeeBv(_)
            | ExprValue::Forall { .. }
            | ExprValue::Exists { .. }
            | ExprValue::Bv2Int(_)
            | ExprValue::Int2Bv(_, _)
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
            | ExprValue::FuncApp { .. } => true,

            // Unknown variant added after compilation
            #[allow(unreachable_patterns)]
            _ => false,
        }
    }
}
