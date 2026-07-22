// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! FP constants, unary operations, arithmetic, and comparisons.
//!
//! IEEE 754 floating-point theory per SMT-LIB2.
//! Classification predicates, conversions, and construction are in `fp_predict`.
//!
//! Part of #5864: bindings expr macro dedup.

use crate::sort::Sort;
use std::sync::Arc;

use super::{Expr, ExprValue, RoundingMode};

/// Predicate: both operands are FP sorts with identical parameters.
fn fp_same(a: &Expr, b: &Expr) -> bool {
    a.sort.is_floating_point() && a.sort == b.sort
}

/// Predicate: operand is an FP sort.
fn is_fp(a: &Expr) -> bool {
    a.sort.is_floating_point()
}

impl Expr {
    // ===== FP Constants (delegate to try_*) =====

    /// Positive infinity for the given FP sort.
    #[must_use]
    pub fn fp_plus_infinity(sort: &Sort) -> Self {
        Self::try_fp_plus_infinity(sort).expect("fp_plus_infinity requires FloatingPoint sort")
    }

    /// Negative infinity for the given FP sort.
    #[must_use]
    pub fn fp_minus_infinity(sort: &Sort) -> Self {
        Self::try_fp_minus_infinity(sort).expect("fp_minus_infinity requires FloatingPoint sort")
    }

    /// NaN for the given FP sort.
    #[must_use]
    pub fn fp_nan(sort: &Sort) -> Self {
        Self::try_fp_nan(sort).expect("fp_nan requires FloatingPoint sort")
    }

    /// Positive zero for the given FP sort.
    #[must_use]
    pub fn fp_plus_zero(sort: &Sort) -> Self {
        Self::try_fp_plus_zero(sort).expect("fp_plus_zero requires FloatingPoint sort")
    }

    /// Negative zero for the given FP sort.
    #[must_use]
    pub fn fp_minus_zero(sort: &Sort) -> Self {
        Self::try_fp_minus_zero(sort).expect("fp_minus_zero requires FloatingPoint sort")
    }

    // ===== Fallible FP Constants =====

    /// Fallible version of [`Expr::fp_plus_infinity`].
    ///
    /// Returns `SortError` if `sort` is not a FloatingPoint sort.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_plus_infinity(sort: &Sort) -> Result<Self, crate::SortError> {
        let (eb, sb) = try_fp_sort_params("fp_plus_infinity", sort)?;
        Ok(Self {
            sort: sort.clone(),
            value: Arc::new(ExprValue::FpPlusInfinity { eb, sb }),
        })
    }

    /// Fallible version of [`Expr::fp_minus_infinity`].
    ///
    /// Returns `SortError` if `sort` is not a FloatingPoint sort.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_minus_infinity(sort: &Sort) -> Result<Self, crate::SortError> {
        let (eb, sb) = try_fp_sort_params("fp_minus_infinity", sort)?;
        Ok(Self {
            sort: sort.clone(),
            value: Arc::new(ExprValue::FpMinusInfinity { eb, sb }),
        })
    }

    /// Fallible version of [`Expr::fp_nan`].
    ///
    /// Returns `SortError` if `sort` is not a FloatingPoint sort.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_nan(sort: &Sort) -> Result<Self, crate::SortError> {
        let (eb, sb) = try_fp_sort_params("fp_nan", sort)?;
        Ok(Self {
            sort: sort.clone(),
            value: Arc::new(ExprValue::FpNaN { eb, sb }),
        })
    }

    /// Fallible version of [`Expr::fp_plus_zero`].
    ///
    /// Returns `SortError` if `sort` is not a FloatingPoint sort.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_plus_zero(sort: &Sort) -> Result<Self, crate::SortError> {
        let (eb, sb) = try_fp_sort_params("fp_plus_zero", sort)?;
        Ok(Self {
            sort: sort.clone(),
            value: Arc::new(ExprValue::FpPlusZero { eb, sb }),
        })
    }

    /// Fallible version of [`Expr::fp_minus_zero`].
    ///
    /// Returns `SortError` if `sort` is not a FloatingPoint sort.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_minus_zero(sort: &Sort) -> Result<Self, crate::SortError> {
        let (eb, sb) = try_fp_sort_params("fp_minus_zero", sort)?;
        Ok(Self {
            sort: sort.clone(),
            value: Arc::new(ExprValue::FpMinusZero { eb, sb }),
        })
    }

    // ===== FP Unary Operations (macro-generated) =====

    unop_same_sort! {
        /// Floating-point absolute value.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_abs / try_fp_abs,
        check: is_fp,
        assert_msg: "fp_abs requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpAbs
    }

    unop_same_sort! {
        /// Floating-point negation.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_neg / try_fp_neg,
        check: is_fp,
        assert_msg: "fp_neg requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpNeg
    }

    // ===== FP Arithmetic (rounding mode — macro-generated) =====

    binop_rm_same_sort! {
        /// Floating-point addition.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_add / try_fp_add,
        check: fp_same,
        assert_msg: "fp_add requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpAdd
    }

    binop_rm_same_sort! {
        /// Floating-point subtraction.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_sub / try_fp_sub,
        check: fp_same,
        assert_msg: "fp_sub requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpSub
    }

    binop_rm_same_sort! {
        /// Floating-point multiplication.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_mul / try_fp_mul,
        check: fp_same,
        assert_msg: "fp_mul requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpMul
    }

    binop_rm_same_sort! {
        /// Floating-point division.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_div / try_fp_div,
        check: fp_same,
        assert_msg: "fp_div requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpDiv
    }

    /// Floating-point fused multiply-add: (fp.fma rm x y z) = x*y + z.
    ///
    /// This is a ternary operation so it stays hand-written; delegates to try_fp_fma.
    #[must_use = "expression operations return a new Expr"]
    #[cfg_attr(kani, kani::requires(self.sort.is_floating_point() && self.sort == y.sort && self.sort == z.sort))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_floating_point()))]
    pub fn fp_fma(self, rm: RoundingMode, y: Self, z: Self) -> Self {
        self.try_fp_fma(rm, y, z)
            .expect("fp_fma requires same FP sorts")
    }

    /// Fallible version of [`Expr::fp_fma`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_fma(self, rm: RoundingMode, y: Self, z: Self) -> Result<Self, crate::SortError> {
        if !(self.sort.is_floating_point() && self.sort == y.sort && self.sort == z.sort) {
            return Err(crate::SortError::Mismatch {
                operation: "fp_fma",
                expected: "three matching FloatingPoint sorts",
                actual: format!("{}, {}, and {}", self.sort, y.sort, z.sort),
            });
        }
        let sort = self.sort.clone();
        Ok(Self {
            sort,
            value: Arc::new(ExprValue::FpFma(rm, self, y, z)),
        })
    }

    unop_rm_same_sort! {
        /// Floating-point square root.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_sqrt / try_fp_sqrt,
        check: is_fp,
        assert_msg: "fp_sqrt requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpSqrt
    }

    // ===== FP Binary Operations (no rounding mode — macro-generated) =====

    binop_same_sort! {
        /// Floating-point remainder.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_rem / try_fp_rem,
        check: fp_same,
        assert_msg: "fp_rem requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpRem
    }

    unop_rm_same_sort! {
        /// Floating-point round to integral.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_round_to_integral / try_fp_round_to_integral,
        check: is_fp,
        assert_msg: "fp_round_to_integral requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpRoundToIntegral
    }

    binop_same_sort! {
        /// Floating-point minimum.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_min / try_fp_min,
        check: fp_same,
        assert_msg: "fp_min requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpMin
    }

    binop_same_sort! {
        /// Floating-point maximum.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_floating_point())]
        fn fp_max / try_fp_max,
        check: fp_same,
        assert_msg: "fp_max requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpMax
    }

    // ===== FP Comparisons (return Bool — macro-generated) =====

    binop_to_bool! {
        /// Floating-point equality (IEEE 754 semantics: NaN != NaN).
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_eq / try_fp_eq,
        check: fp_same,
        assert_msg: "fp_eq requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpEq
    }

    binop_to_bool! {
        /// Floating-point less than.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_lt / try_fp_lt,
        check: fp_same,
        assert_msg: "fp_lt requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpLt
    }

    binop_to_bool! {
        /// Floating-point less than or equal.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_le / try_fp_le,
        check: fp_same,
        assert_msg: "fp_le requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpLe
    }

    binop_to_bool! {
        /// Floating-point greater than.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_gt / try_fp_gt,
        check: fp_same,
        assert_msg: "fp_gt requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpGt
    }

    binop_to_bool! {
        /// Floating-point greater than or equal.
        /// REQUIRES: `self` and `other` are FP sorts with identical parameters.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_ge / try_fp_ge,
        check: fp_same,
        assert_msg: "fp_ge requires same FP sorts",
        error_expected: "matching FloatingPoint sorts",
        variant: FpGe
    }
}

/// Fallible extraction of (eb, sb) from a floating-point sort.
fn try_fp_sort_params(
    operation: &'static str,
    sort: &Sort,
) -> Result<(u32, u32), crate::SortError> {
    let eb = sort
        .fp_exponent_bits()
        .ok_or_else(|| crate::SortError::unary(operation, "FloatingPoint", sort))?;
    let sb = sort
        .fp_significand_bits()
        .ok_or_else(|| crate::SortError::unary(operation, "FloatingPoint", sort))?;
    Ok((eb, sb))
}

#[cfg(test)]
#[path = "fp_tests.rs"]
mod tests;
