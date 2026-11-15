// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Bitvector comparison operations.

use super::{bv_same, Expr};

impl Expr {
    // ===== Comparison Operations =====

    binop_to_bool! {
        /// Unsigned less than.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        fn bvult / try_bvult,
        check: bv_same,
        assert_msg: "bvult requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvULt
    }

    binop_to_bool! {
        /// Unsigned less than or equal.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        fn bvule / try_bvule,
        check: bv_same,
        assert_msg: "bvule requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvULe
    }

    binop_to_bool! {
        /// Unsigned greater than.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        fn bvugt / try_bvugt,
        check: bv_same,
        assert_msg: "bvugt requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvUGt
    }

    binop_to_bool! {
        /// Unsigned greater than or equal.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        fn bvuge / try_bvuge,
        check: bv_same,
        assert_msg: "bvuge requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvUGe
    }

    binop_to_bool! {
        /// Signed less than.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        fn bvslt / try_bvslt,
        check: bv_same,
        assert_msg: "bvslt requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvSLt
    }

    binop_to_bool! {
        /// Signed less than or equal.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        fn bvsle / try_bvsle,
        check: bv_same,
        assert_msg: "bvsle requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvSLe
    }

    binop_to_bool! {
        /// Signed greater than.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        fn bvsgt / try_bvsgt,
        check: bv_same,
        assert_msg: "bvsgt requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvSGt
    }

    binop_to_bool! {
        /// Signed greater than or equal.
        /// REQUIRES: `self` and `other` are BitVec sorts with identical widths.
        /// ENSURES: result sort is Bool.
        fn bvsge / try_bvsge,
        check: bv_same,
        assert_msg: "bvsge requires same BitVec sorts",
        error_expected: "matching BitVec sorts",
        variant: BvSGe
    }
}
