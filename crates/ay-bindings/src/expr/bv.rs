// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Bitvector operations for AY expressions.

mod comparison;

use crate::sort::Sort;
use std::sync::Arc;

use super::{Expr, ExprValue};

/// Predicate: both operands are BitVec sorts with identical widths.
fn bv_same(a: &Expr, b: &Expr) -> bool {
    a.sort.is_bitvec() && a.sort == b.sort
}

/// Predicate: operand is a BitVec sort.
fn is_bv(a: &Expr) -> bool {
    a.sort.is_bitvec()
}

impl Expr {
    // ===== Bitvector Arithmetic Operations =====

    binop_same_sort! {
        /// Bitvector addition.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvadd / try_bvadd,
        check: bv_same,
        assert_msg: "bvadd requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvAdd
    }

    binop_same_sort! {
        /// Bitvector subtraction.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvsub / try_bvsub,
        check: bv_same,
        assert_msg: "bvsub requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvSub
    }

    binop_same_sort! {
        /// Bitvector multiplication.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvmul / try_bvmul,
        check: bv_same,
        assert_msg: "bvmul requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvMul
    }

    binop_same_sort! {
        /// Unsigned bitvector division.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvudiv / try_bvudiv,
        check: bv_same,
        assert_msg: "bvudiv requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvUDiv
    }

    binop_same_sort! {
        /// Signed bitvector division.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvsdiv / try_bvsdiv,
        check: bv_same,
        assert_msg: "bvsdiv requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvSDiv
    }

    binop_same_sort! {
        /// Unsigned bitvector remainder.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvurem / try_bvurem,
        check: bv_same,
        assert_msg: "bvurem requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvURem
    }

    binop_same_sort! {
        /// Signed bitvector remainder.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvsrem / try_bvsrem,
        check: bv_same,
        assert_msg: "bvsrem requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvSRem
    }

    // ===== Unary Operations =====

    unop_same_sort! {
        /// Bitvector negation.
        /// REQUIRES: `self` is a BitVec sort.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec())]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvneg / try_bvneg,
        check: is_bv,
        assert_msg: "bvneg requires BitVec sort",
        error_expected: "BitVec",
        variant: BvNeg
    }

    // ===== Bitwise Operations =====

    unop_same_sort! {
        /// Bitwise NOT.
        /// REQUIRES: `self` is a BitVec sort.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec())]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvnot / try_bvnot,
        check: is_bv,
        assert_msg: "bvnot requires BitVec sort",
        error_expected: "BitVec",
        variant: BvNot
    }

    binop_same_sort! {
        /// Bitwise AND.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvand / try_bvand,
        check: bv_same,
        assert_msg: "bvand requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvAnd
    }

    binop_same_sort! {
        /// Bitwise OR.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvor / try_bvor,
        check: bv_same,
        assert_msg: "bvor requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvOr
    }

    binop_same_sort! {
        /// Bitwise XOR.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvxor / try_bvxor,
        check: bv_same,
        assert_msg: "bvxor requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvXor
    }

    // ===== Shift Operations =====

    binop_same_sort! {
        /// Logical shift left.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvshl / try_bvshl,
        check: bv_same,
        assert_msg: "bvshl requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvShl
    }

    binop_same_sort! {
        /// Logical shift right.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvlshr / try_bvlshr,
        check: bv_same,
        assert_msg: "bvlshr requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvLShr
    }

    binop_same_sort! {
        /// Arithmetic shift right.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort matches operand sort.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bitvec())]
        fn bvashr / try_bvashr,
        check: bv_same,
        assert_msg: "bvashr requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvAShr
    }

    // ===== Extension and Extraction Operations =====
    // These have non-standard parameter shapes and remain hand-written.

    /// Zero extend to wider bitvector.
    /// REQUIRES: `self` is a BitVec sort.
    /// ENSURES: result sort width = self.width + extra_bits.
    ///
    /// # Panics
    /// Panics if `self` is not BitVec-sorted. Only call this on terms whose
    /// sort is a locally-guaranteed invariant; for externally-sourced terms
    /// use [`Expr::try_zero_extend`] and fail closed on the error.
    #[cfg_attr(kani, kani::requires(self.sort.is_bitvec()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bitvec()))]
    #[must_use = "expression operations return a new Expr"]
    #[track_caller]
    pub fn zero_extend(self, extra_bits: u32) -> Self {
        self.try_zero_extend(extra_bits)
            .expect("zero_extend requires BitVec sort")
    }

    /// Sign extend to wider bitvector.
    /// REQUIRES: `self` is a BitVec sort.
    /// ENSURES: result sort width = self.width + extra_bits.
    ///
    /// # Panics
    /// Panics if `self` is not BitVec-sorted. Only call this on terms whose
    /// sort is a locally-guaranteed invariant; for externally-sourced terms
    /// use [`Expr::try_sign_extend`] and fail closed on the error.
    #[cfg_attr(kani, kani::requires(self.sort.is_bitvec()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bitvec()))]
    #[must_use = "expression operations return a new Expr"]
    #[track_caller]
    pub fn sign_extend(self, extra_bits: u32) -> Self {
        self.try_sign_extend(extra_bits)
            .expect("sign_extend requires BitVec sort")
    }

    /// Extract bits `[high:low]` (inclusive).
    /// REQUIRES: `self` is a BitVec sort and 0 <= low <= high < width.
    /// ENSURES: result sort width = high - low + 1.
    ///
    /// # Panics
    /// Panics if `self` is not BitVec-sorted or the bit range is invalid.
    /// Only call this on terms whose sort is a locally-guaranteed invariant;
    /// for externally-sourced terms (e.g. an embedder lowering its own IR into
    /// `Expr`s) use [`Expr::try_extract`] and fail closed on the error — an
    /// Int-sorted operand reaching this wrapper aborts the whole embedding
    /// process (development verifier census failure). `#[track_caller]` attributes the
    /// panic to the emitting call site, not this wrapper.
    #[cfg_attr(kani, kani::requires(self.sort.is_bitvec()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bitvec()))]
    #[must_use = "expression operations return a new Expr"]
    #[track_caller]
    pub fn extract(self, high: u32, low: u32) -> Self {
        self.try_extract(high, low)
            .expect("extract requires BitVec sort with valid bit range")
    }

    /// Concatenate two bitvectors.
    /// REQUIRES: `self` and `other` are BitVec sorts.
    /// ENSURES: result sort width = self.width + other.width.
    ///
    /// # Panics
    /// Panics if `self` or `other` is not BitVec-sorted. Only call this on
    /// terms whose sorts are locally-guaranteed invariants; for
    /// externally-sourced terms use [`Expr::try_concat`] and fail closed on
    /// the error.
    #[cfg_attr(kani, kani::requires(self.sort.is_bitvec() && other.sort.is_bitvec()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bitvec()))]
    #[must_use = "expression operations return a new Expr"]
    #[track_caller]
    pub fn concat(self, other: Self) -> Self {
        self.try_concat(other)
            .expect("concat requires BitVec sorts")
    }

    // ===== BV-Int Conversions =====

    unop_to_sort! {
        /// Convert bitvector to integer.
        /// REQUIRES: `self` is a BitVec sort.
        /// ENSURES: result sort is Int.
        ///
        /// The result is an unbounded integer with the unsigned value of the bitvector.
        /// In SMT-LIB: (bv2int bv).
        #[kani_requires(self.sort.is_bitvec())]
        #[kani_ensures(|result: &Self| result.sort.is_int())]
        fn bv2int / try_bv2int,
        check: is_bv,
        assert_msg: "bv2int requires BitVec sort",
        error_expected: "BitVec",
        result_sort: Sort::int(),
        variant: Bv2Int
    }

    /// Convert bitvector to signed integer.
    /// REQUIRES: `self` is a BitVec sort.
    /// ENSURES: result sort is Int.
    ///
    /// The result is an unbounded integer with the signed (two's complement)
    /// value of the bitvector. For an n-bit bitvector:
    /// - If MSB is 0: result = unsigned value
    /// - If MSB is 1: result = unsigned value - 2^n
    ///
    /// Part of #911: BigInt::from signed conversion for CHC.
    ///
    /// # Panics
    /// Panics if `self` is not BitVec-sorted; for externally-sourced terms
    /// use [`Expr::try_bv2int_signed`] and fail closed on the error.
    #[cfg_attr(kani, kani::requires(self.sort.is_bitvec()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_int()))]
    #[must_use = "expression operations return a new Expr"]
    #[track_caller]
    pub fn bv2int_signed(self) -> Self {
        self.try_bv2int_signed()
            .expect("bv2int_signed requires BitVec sort")
    }

    /// Fallible version of [`Expr::bv2int_signed`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_bv2int_signed(self) -> Result<Self, crate::SortError> {
        if !self.sort.is_bitvec() {
            return Err(crate::SortError::unary(
                "bv2int_signed",
                "BitVec",
                &self.sort,
            ));
        }
        let width = self
            .sort
            .bitvec_width()
            .expect("bitvec_width should succeed after is_bitvec check");

        // Extract MSB (sign bit)
        let msb = self.clone().extract(width - 1, width - 1);
        let msb_is_one = msb.eq(Self::bitvec_const(1u64, 1));

        // Compute unsigned value
        let unsigned = self.bv2int();

        // Compute 2^width as Int constant
        let two_pow_width = if width < 128 {
            let val: u128 = 1u128 << width;
            Self::int_const(val)
        } else {
            use num_bigint::BigInt;
            let val = BigInt::from(1u128) << width;
            Self::int_const(val)
        };

        // If MSB is 1: unsigned - 2^width, else: unsigned
        Ok(Self::ite(
            msb_is_one,
            unsigned.clone().int_sub(two_pow_width),
            unsigned,
        ))
    }

    // ===== Fallible variants for non-macro operations =====

    /// Fallible version of [`Expr::zero_extend`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_zero_extend(self, extra_bits: u32) -> Result<Self, crate::SortError> {
        if !self.sort.is_bitvec() {
            return Err(crate::SortError::unary("zero_extend", "BitVec", &self.sort));
        }
        let old_width = self.sort.bitvec_width().expect("is_bitvec checked");
        let new_width =
            old_width
                .checked_add(extra_bits)
                .ok_or_else(|| crate::SortError::Mismatch {
                    operation: "zero_extend",
                    expected: "non-overflowing width",
                    actual: format!("{old_width} + {extra_bits} overflows u32"),
                })?;
        Ok(Self {
            sort: Sort::bitvec(new_width),
            value: Arc::new(ExprValue::BvZeroExtend {
                expr: self,
                extra_bits,
            }),
        })
    }

    /// Fallible version of [`Expr::sign_extend`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_sign_extend(self, extra_bits: u32) -> Result<Self, crate::SortError> {
        if !self.sort.is_bitvec() {
            return Err(crate::SortError::unary("sign_extend", "BitVec", &self.sort));
        }
        let old_width = self.sort.bitvec_width().expect("is_bitvec checked");
        let new_width =
            old_width
                .checked_add(extra_bits)
                .ok_or_else(|| crate::SortError::Mismatch {
                    operation: "sign_extend",
                    expected: "non-overflowing width",
                    actual: format!("{old_width} + {extra_bits} overflows u32"),
                })?;
        Ok(Self {
            sort: Sort::bitvec(new_width),
            value: Arc::new(ExprValue::BvSignExtend {
                expr: self,
                extra_bits,
            }),
        })
    }

    /// Fallible version of [`Expr::extract`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_extract(self, high: u32, low: u32) -> Result<Self, crate::SortError> {
        if !self.sort.is_bitvec() {
            return Err(crate::SortError::unary("extract", "BitVec", &self.sort));
        }
        let old_width = self.sort.bitvec_width().expect("is_bitvec checked");
        if high < low || high >= old_width {
            return Err(crate::SortError::Mismatch {
                operation: "extract",
                expected: "0 <= low <= high < width",
                actual: format!("high={high}, low={low}, width={old_width}"),
            });
        }
        let new_width = high - low + 1;
        Ok(Self {
            sort: Sort::bitvec(new_width),
            value: Arc::new(ExprValue::BvExtract {
                expr: self,
                high,
                low,
            }),
        })
    }

    /// Fallible version of [`Expr::concat`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_concat(self, other: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_bitvec() || !other.sort.is_bitvec() {
            return Err(crate::SortError::binary(
                "concat",
                "BitVec sorts",
                &self.sort,
                &other.sort,
            ));
        }
        let w1 = self.sort.bitvec_width().expect("is_bitvec checked");
        let w2 = other.sort.bitvec_width().expect("is_bitvec checked");
        let new_width = w1
            .checked_add(w2)
            .ok_or_else(|| crate::SortError::Mismatch {
                operation: "concat",
                expected: "non-overflowing width",
                actual: format!("{w1} + {w2} overflows u32"),
            })?;
        Ok(Self {
            sort: Sort::bitvec(new_width),
            value: Arc::new(ExprValue::BvConcat(self, other)),
        })
    }
}
