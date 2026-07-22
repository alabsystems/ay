// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! FP classification predicates, conversions, and construction.
//!
//! Constants, unary operations, arithmetic, and comparisons are in `fp`.

use crate::sort::Sort;
use std::sync::Arc;

use super::{Expr, ExprValue, RoundingMode};

fn is_fp(a: &Expr) -> bool {
    a.sort.is_floating_point()
}

impl Expr {
    // ===== FP Classification Predicates (return Bool — macro-generated) =====

    unop_to_bool! {
        /// Test if floating-point value is NaN.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_is_nan / try_fp_is_nan,
        check: is_fp,
        assert_msg: "fp_is_nan requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpIsNaN
    }

    unop_to_bool! {
        /// Test if floating-point value is infinite.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_is_infinite / try_fp_is_infinite,
        check: is_fp,
        assert_msg: "fp_is_infinite requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpIsInfinite
    }

    unop_to_bool! {
        /// Test if floating-point value is zero (positive or negative).
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_is_zero / try_fp_is_zero,
        check: is_fp,
        assert_msg: "fp_is_zero requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpIsZero
    }

    unop_to_bool! {
        /// Test if floating-point value is normal.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_is_normal / try_fp_is_normal,
        check: is_fp,
        assert_msg: "fp_is_normal requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpIsNormal
    }

    unop_to_bool! {
        /// Test if floating-point value is subnormal.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_is_subnormal / try_fp_is_subnormal,
        check: is_fp,
        assert_msg: "fp_is_subnormal requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpIsSubnormal
    }

    unop_to_bool! {
        /// Test if floating-point value is positive.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_is_positive / try_fp_is_positive,
        check: is_fp,
        assert_msg: "fp_is_positive requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpIsPositive
    }

    unop_to_bool! {
        /// Test if floating-point value is negative.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn fp_is_negative / try_fp_is_negative,
        check: is_fp,
        assert_msg: "fp_is_negative requires FP sort",
        error_expected: "FloatingPoint",
        variant: FpIsNegative
    }

    // ===== FP Conversions =====

    /// Convert FP to signed bitvector of given width.
    #[must_use = "expression operations return a new Expr"]
    #[cfg_attr(kani, kani::requires(self.sort.is_floating_point()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bitvec()))]
    pub fn fp_to_sbv(self, rm: RoundingMode, width: u32) -> Self {
        self.try_fp_to_sbv(rm, width)
            .expect("fp_to_sbv requires FP sort")
    }

    /// Fallible version of [`Expr::fp_to_sbv`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_to_sbv(self, rm: RoundingMode, width: u32) -> Result<Self, crate::SortError> {
        if !self.sort.is_floating_point() {
            return Err(crate::SortError::unary(
                "fp_to_sbv",
                "FloatingPoint",
                &self.sort,
            ));
        }
        Ok(Self {
            sort: Sort::bitvec(width),
            value: Arc::new(ExprValue::FpToSbv(rm, self, width)),
        })
    }

    /// Convert FP to unsigned bitvector of given width.
    #[must_use = "expression operations return a new Expr"]
    #[cfg_attr(kani, kani::requires(self.sort.is_floating_point()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bitvec()))]
    pub fn fp_to_ubv(self, rm: RoundingMode, width: u32) -> Self {
        self.try_fp_to_ubv(rm, width)
            .expect("fp_to_ubv requires FP sort")
    }

    /// Fallible version of [`Expr::fp_to_ubv`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_to_ubv(self, rm: RoundingMode, width: u32) -> Result<Self, crate::SortError> {
        if !self.sort.is_floating_point() {
            return Err(crate::SortError::unary(
                "fp_to_ubv",
                "FloatingPoint",
                &self.sort,
            ));
        }
        Ok(Self {
            sort: Sort::bitvec(width),
            value: Arc::new(ExprValue::FpToUbv(rm, self, width)),
        })
    }

    unop_to_sort! {
        /// Convert FP to real number.
        /// REQUIRES: `self` is an FP sort.
        /// ENSURES: result sort is Real.
        #[kani_requires(self.sort.is_floating_point())]
        #[kani_ensures(|result: &Self| result.sort.is_real())]
        fn fp_to_real / try_fp_to_real,
        check: is_fp,
        assert_msg: "fp_to_real requires FP sort",
        error_expected: "FloatingPoint",
        result_sort: Sort::real(),
        variant: FpToReal
    }

    /// Convert FP to IEEE 754 bitvector (bit-pattern reinterpretation, no rounding mode).
    ///
    /// SMT-LIB: `(fp.to_ieee_bv x)`
    /// Result sort: `(_ BitVec (eb + sb))` for `(_ FloatingPoint eb sb)` input.
    #[must_use = "expression operations return a new Expr"]
    #[cfg_attr(kani, kani::requires(self.sort.is_floating_point()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bitvec()))]
    pub fn fp_to_ieee_bv(self) -> Self {
        self.try_fp_to_ieee_bv()
            .expect("fp_to_ieee_bv requires FP sort")
    }

    /// Fallible version of [`Expr::fp_to_ieee_bv`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_to_ieee_bv(self) -> Result<Self, crate::SortError> {
        if !self.sort.is_floating_point() {
            return Err(crate::SortError::unary(
                "fp_to_ieee_bv",
                "FloatingPoint",
                &self.sort,
            ));
        }
        let eb = self.sort.fp_exponent_bits().expect("FP sort has eb");
        let sb = self.sort.fp_significand_bits().expect("FP sort has sb");
        Ok(Self {
            sort: Sort::bitvec(eb + sb),
            value: Arc::new(ExprValue::FpToIeeeBv(self)),
        })
    }

    // ===== FP Construction and Conversion TO FP =====

    /// Construct FP from sign (1-bit BV), exponent (eb-bit BV), significand ((sb-1)-bit BV).
    ///
    /// SMT-LIB: `(fp sign exp sig)`
    #[must_use]
    #[cfg_attr(kani, kani::requires(
        sign.sort.is_bitvec() && exponent.sort.is_bitvec() && significand.sort.is_bitvec()
    ))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_floating_point()))]
    pub fn fp_from_bvs(sign: Self, exponent: Self, significand: Self) -> Self {
        Self::try_fp_from_bvs(sign, exponent, significand)
            .expect("fp_from_bvs requires BV sorts with sign=1-bit")
    }

    /// Fallible version of [`Expr::fp_from_bvs`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_from_bvs(
        sign: Self,
        exponent: Self,
        significand: Self,
    ) -> Result<Self, crate::SortError> {
        if !sign.sort.is_bitvec() {
            return Err(crate::SortError::unary(
                "fp_from_bvs (sign)",
                "BitVec",
                &sign.sort,
            ));
        }
        if !exponent.sort.is_bitvec() {
            return Err(crate::SortError::unary(
                "fp_from_bvs (exponent)",
                "BitVec",
                &exponent.sort,
            ));
        }
        if !significand.sort.is_bitvec() {
            return Err(crate::SortError::unary(
                "fp_from_bvs (significand)",
                "BitVec",
                &significand.sort,
            ));
        }
        let sign_w = sign.sort.bitvec_width().expect("sign width");
        if sign_w != 1 {
            return Err(crate::SortError::Mismatch {
                operation: "fp_from_bvs",
                expected: "1-bit BitVec for sign",
                actual: format!("BitVec({sign_w})"),
            });
        }
        let eb = exponent.sort.bitvec_width().expect("exponent width");
        let sb_minus_1 = significand.sort.bitvec_width().expect("significand width");
        let sb = sb_minus_1 + 1;
        Ok(Self {
            sort: Sort::fp(eb, sb),
            value: Arc::new(ExprValue::FpFromBvs(sign, exponent, significand)),
        })
    }

    /// Convert bitvector to FP (interpret BV bits as IEEE 754 representation).
    ///
    /// SMT-LIB: `((_ to_fp eb sb) rm bv)` where bv has width eb+sb.
    #[must_use = "expression operations return a new Expr"]
    #[cfg_attr(kani, kani::requires(self.sort.is_bitvec()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_floating_point()))]
    pub fn bv_to_fp(self, rm: RoundingMode, eb: u32, sb: u32) -> Self {
        self.try_bv_to_fp(rm, eb, sb)
            .expect("bv_to_fp requires BV sort")
    }

    /// Fallible version of [`Expr::bv_to_fp`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_bv_to_fp(
        self,
        rm: RoundingMode,
        eb: u32,
        sb: u32,
    ) -> Result<Self, crate::SortError> {
        if !self.sort.is_bitvec() {
            return Err(crate::SortError::unary("bv_to_fp", "BitVec", &self.sort));
        }
        Ok(Self {
            sort: Sort::fp(eb, sb),
            value: Arc::new(ExprValue::BvToFp(rm, self, eb, sb)),
        })
    }

    /// Convert unsigned bitvector to FP.
    ///
    /// SMT-LIB: `((_ to_fp_unsigned eb sb) rm bv)`
    #[must_use = "expression operations return a new Expr"]
    #[cfg_attr(kani, kani::requires(self.sort.is_bitvec()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_floating_point()))]
    pub fn bv_to_fp_unsigned(self, rm: RoundingMode, eb: u32, sb: u32) -> Self {
        self.try_bv_to_fp_unsigned(rm, eb, sb)
            .expect("bv_to_fp_unsigned requires BV sort")
    }

    /// Fallible version of [`Expr::bv_to_fp_unsigned`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_bv_to_fp_unsigned(
        self,
        rm: RoundingMode,
        eb: u32,
        sb: u32,
    ) -> Result<Self, crate::SortError> {
        if !self.sort.is_bitvec() {
            return Err(crate::SortError::unary(
                "bv_to_fp_unsigned",
                "BitVec",
                &self.sort,
            ));
        }
        Ok(Self {
            sort: Sort::fp(eb, sb),
            value: Arc::new(ExprValue::BvToFpUnsigned(rm, self, eb, sb)),
        })
    }

    /// Convert FP to a different FP precision.
    ///
    /// SMT-LIB: `((_ to_fp eb sb) rm fp)`
    #[must_use = "expression operations return a new Expr"]
    #[cfg_attr(kani, kani::requires(self.sort.is_floating_point()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_floating_point()))]
    pub fn fp_to_fp(self, rm: RoundingMode, eb: u32, sb: u32) -> Self {
        self.try_fp_to_fp(rm, eb, sb)
            .expect("fp_to_fp requires FP sort")
    }

    /// Fallible version of [`Expr::fp_to_fp`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fp_to_fp(
        self,
        rm: RoundingMode,
        eb: u32,
        sb: u32,
    ) -> Result<Self, crate::SortError> {
        if !self.sort.is_floating_point() {
            return Err(crate::SortError::unary(
                "fp_to_fp",
                "FloatingPoint",
                &self.sort,
            ));
        }
        Ok(Self {
            sort: Sort::fp(eb, sb),
            value: Arc::new(ExprValue::FpToFp(rm, self, eb, sb)),
        })
    }
}
