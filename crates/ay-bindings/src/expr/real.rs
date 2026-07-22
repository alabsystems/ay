// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Real (rational) operations for AY expressions.
//!
//! Part of #911: BigRational interception for CHC codegen.
//! SMT-LIB Real arithmetic on rational inputs produces rational outputs
//! for +, -, *, / operations (no transcendentals or square roots).

use crate::sort::Sort;

use super::Expr;

/// Predicate: both operands are Real sorts.
fn real_same(a: &Expr, b: &Expr) -> bool {
    a.sort.is_real() && b.sort.is_real()
}

/// Predicate: operand is a Real sort.
fn is_real(a: &Expr) -> bool {
    a.sort.is_real()
}

/// Predicate: operand is an Int sort.
fn is_int(a: &Expr) -> bool {
    a.sort.is_int()
}

impl Expr {
    // ===== Int to Real Conversion =====

    unop_to_sort! {
        /// Convert Int to Real.
        /// REQUIRES: `self` is an Int sort.
        /// ENSURES: result sort is Real.
        #[kani_requires(self.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_real())]
        fn int_to_real / try_int_to_real,
        check: is_int,
        assert_msg: "int_to_real requires Int sort",
        error_expected: "Int",
        result_sort: Sort::real(),
        variant: IntToReal
    }

    unop_to_sort! {
        /// Convert Real to Int (floor).
        /// SMT-LIB: (to_int r) returns floor(r).
        /// REQUIRES: `self` is a Real sort.
        /// ENSURES: result sort is Int.
        #[kani_requires(self.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_int())]
        fn real_to_int / try_real_to_int,
        check: is_real,
        assert_msg: "real_to_int requires Real sort",
        error_expected: "Real",
        result_sort: Sort::int(),
        variant: RealToInt
    }

    unop_to_bool! {
        /// Test if Real is integral (is_int predicate).
        /// SMT-LIB: (is_int r) returns true iff r is an integer value.
        /// REQUIRES: `self` is a Real sort.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn is_int / try_is_int,
        check: is_real,
        assert_msg: "is_int requires Real sort",
        error_expected: "Real",
        variant: IsInt
    }

    // ===== Real Arithmetic Operations =====

    binop_same_sort! {
        /// Real addition.
        /// REQUIRES: `self` and `other` are Real sorts.
        /// ENSURES: result sort is Real.
        #[kani_requires(self.sort.is_real() && other.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_real())]
        fn real_add / try_real_add,
        check: real_same,
        assert_msg: "real_add requires Real sorts",
        error_expected: "Real sorts",
        variant: RealAdd
    }

    binop_same_sort! {
        /// Real subtraction.
        /// REQUIRES: `self` and `other` are Real sorts.
        /// ENSURES: result sort is Real.
        #[kani_requires(self.sort.is_real() && other.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_real())]
        fn real_sub / try_real_sub,
        check: real_same,
        assert_msg: "real_sub requires Real sorts",
        error_expected: "Real sorts",
        variant: RealSub
    }

    binop_same_sort! {
        /// Real multiplication.
        /// REQUIRES: `self` and `other` are Real sorts.
        /// ENSURES: result sort is Real.
        #[kani_requires(self.sort.is_real() && other.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_real())]
        fn real_mul / try_real_mul,
        check: real_same,
        assert_msg: "real_mul requires Real sorts",
        error_expected: "Real sorts",
        variant: RealMul
    }

    binop_same_sort! {
        /// Real division.
        /// REQUIRES: `self` and `other` are Real sorts.
        /// ENSURES: result sort is Real.
        #[kani_requires(self.sort.is_real() && other.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_real())]
        fn real_div / try_real_div,
        check: real_same,
        assert_msg: "real_div requires Real sorts",
        error_expected: "Real sorts",
        variant: RealDiv
    }

    unop_same_sort! {
        /// Real negation.
        /// REQUIRES: `self` is a Real sort.
        /// ENSURES: result sort is Real.
        #[kani_requires(self.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_real())]
        fn real_neg / try_real_neg,
        check: is_real,
        assert_msg: "real_neg requires Real sort",
        error_expected: "Real",
        variant: RealNeg
    }

    // ===== Real Comparison Operations =====

    binop_to_bool! {
        /// Real less than.
        /// REQUIRES: `self` and `other` are Real sorts.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_real() && other.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn real_lt / try_real_lt,
        check: real_same,
        assert_msg: "real_lt requires Real sorts",
        error_expected: "Real sorts",
        variant: RealLt
    }

    binop_to_bool! {
        /// Real less than or equal.
        /// REQUIRES: `self` and `other` are Real sorts.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_real() && other.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn real_le / try_real_le,
        check: real_same,
        assert_msg: "real_le requires Real sorts",
        error_expected: "Real sorts",
        variant: RealLe
    }

    binop_to_bool! {
        /// Real greater than.
        /// REQUIRES: `self` and `other` are Real sorts.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_real() && other.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn real_gt / try_real_gt,
        check: real_same,
        assert_msg: "real_gt requires Real sorts",
        error_expected: "Real sorts",
        variant: RealGt
    }

    binop_to_bool! {
        /// Real greater than or equal.
        /// REQUIRES: `self` and `other` are Real sorts.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_real() && other.sort.is_real())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn real_ge / try_real_ge,
        check: real_same,
        assert_msg: "real_ge requires Real sorts",
        error_expected: "Real sorts",
        variant: RealGe
    }
}
