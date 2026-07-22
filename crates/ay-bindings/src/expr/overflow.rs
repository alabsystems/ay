// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Overflow detection operations for AY expressions.
//!
//! These operations return a Bool indicating whether an arithmetic operation
//! would overflow or underflow.

use super::Expr;

/// Predicate: both operands are BitVec sorts with identical widths.
fn bv_same(a: &Expr, b: &Expr) -> bool {
    a.sort.is_bitvec() && a.sort == b.sort
}

/// Predicate: operand is a BitVec sort.
fn is_bv(a: &Expr) -> bool {
    a.sort.is_bitvec()
}

impl Expr {
    // ===== Overflow Detection Operations =====

    binop_to_bool! {
        /// Check that unsigned addition does not overflow.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        ///
        /// Returns true if a + b does NOT overflow (i.e., the result fits in the bit-width).
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn bvadd_no_overflow_unsigned / try_bvadd_no_overflow_unsigned,
        check: bv_same,
        assert_msg: "bvadd_no_overflow_unsigned requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvAddNoOverflowUnsigned
    }

    binop_to_bool! {
        /// Check that signed addition does not overflow.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        ///
        /// Returns true if a + b does NOT overflow (result is representable in signed bit-width).
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn bvadd_no_overflow_signed / try_bvadd_no_overflow_signed,
        check: bv_same,
        assert_msg: "bvadd_no_overflow_signed requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvAddNoOverflowSigned
    }

    binop_to_bool! {
        /// Check that unsigned subtraction does not underflow.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        ///
        /// Returns true if a - b does NOT underflow (i.e., a >= b).
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn bvsub_no_underflow_unsigned / try_bvsub_no_underflow_unsigned,
        check: bv_same,
        assert_msg: "bvsub_no_underflow_unsigned requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvSubNoUnderflowUnsigned
    }

    binop_to_bool! {
        /// Check that signed subtraction does not overflow.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        ///
        /// Returns true if a - b does NOT overflow.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn bvsub_no_overflow_signed / try_bvsub_no_overflow_signed,
        check: bv_same,
        assert_msg: "bvsub_no_overflow_signed requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvSubNoOverflowSigned
    }

    binop_to_bool! {
        /// Check that unsigned multiplication does not overflow.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        ///
        /// Returns true if a * b does NOT overflow.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn bvmul_no_overflow_unsigned / try_bvmul_no_overflow_unsigned,
        check: bv_same,
        assert_msg: "bvmul_no_overflow_unsigned requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvMulNoOverflowUnsigned
    }

    binop_to_bool! {
        /// Check that signed multiplication does not overflow.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        ///
        /// Returns true if a * b does NOT overflow.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn bvmul_no_overflow_signed / try_bvmul_no_overflow_signed,
        check: bv_same,
        assert_msg: "bvmul_no_overflow_signed requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvMulNoOverflowSigned
    }

    unop_to_bool! {
        /// Check that signed negation does not overflow.
        /// REQUIRES: `self` is a BitVec sort.
        /// ENSURES: result sort is Bool.
        ///
        /// Returns true if -a does NOT overflow.
        /// Negation overflow only occurs for INT_MIN (e.g., -128 for i8).
        #[kani_requires(self.sort.is_bitvec())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn bvneg_no_overflow / try_bvneg_no_overflow,
        check: is_bv,
        assert_msg: "bvneg_no_overflow requires BitVec sort",
        error_expected: "BitVec",
        variant: BvNegNoOverflow
    }

    binop_to_bool! {
        /// Check that signed division does not overflow.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        ///
        /// Returns true if a / b does NOT overflow.
        /// Signed division overflow only occurs when dividing INT_MIN by -1.
        #[kani_requires(self.sort.is_bitvec() && self.sort == other.sort)]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn bvsdiv_no_overflow / try_bvsdiv_no_overflow,
        check: bv_same,
        assert_msg: "bvsdiv_no_overflow requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvSdivNoOverflow
    }
}
