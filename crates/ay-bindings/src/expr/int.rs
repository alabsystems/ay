// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Integer (unbounded) operations for AY expressions.

use crate::sort::Sort;
use std::sync::Arc;

use super::{Expr, ExprValue};

/// Predicate: both operands are Int sorts.
fn int_same(a: &Expr, b: &Expr) -> bool {
    a.sort.is_int() && b.sort.is_int()
}

/// Predicate: operand is an Int sort.
fn is_int(a: &Expr) -> bool {
    a.sort.is_int()
}

impl Expr {
    // ===== Integer Arithmetic Operations =====

    binop_same_sort! {
        /// Integer addition.
        /// REQUIRES: `self` and `other` are Int sorts.
        /// ENSURES: result sort is Int.
        #[kani_requires(self.sort.is_int() && other.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_int())]
        fn int_add / try_int_add,
        check: int_same,
        assert_msg: "int_add requires Int sorts",
        error_expected: "Int sorts",
        variant: IntAdd
    }

    binop_same_sort! {
        /// Integer subtraction.
        /// REQUIRES: `self` and `other` are Int sorts.
        /// ENSURES: result sort is Int.
        #[kani_requires(self.sort.is_int() && other.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_int())]
        fn int_sub / try_int_sub,
        check: int_same,
        assert_msg: "int_sub requires Int sorts",
        error_expected: "Int sorts",
        variant: IntSub
    }

    binop_same_sort! {
        /// Integer multiplication.
        /// REQUIRES: `self` and `other` are Int sorts.
        /// ENSURES: result sort is Int.
        #[kani_requires(self.sort.is_int() && other.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_int())]
        fn int_mul / try_int_mul,
        check: int_same,
        assert_msg: "int_mul requires Int sorts",
        error_expected: "Int sorts",
        variant: IntMul
    }

    binop_same_sort! {
        /// Integer division.
        /// REQUIRES: `self` and `other` are Int sorts.
        /// ENSURES: result sort is Int.
        #[kani_requires(self.sort.is_int() && other.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_int())]
        fn int_div / try_int_div,
        check: int_same,
        assert_msg: "int_div requires Int sorts",
        error_expected: "Int sorts",
        variant: IntDiv
    }

    binop_same_sort! {
        /// Integer modulo.
        /// REQUIRES: `self` and `other` are Int sorts.
        /// ENSURES: result sort is Int.
        #[kani_requires(self.sort.is_int() && other.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_int())]
        fn int_mod / try_int_mod,
        check: int_same,
        assert_msg: "int_mod requires Int sorts",
        error_expected: "Int sorts",
        variant: IntMod
    }

    unop_same_sort! {
        /// Integer negation.
        /// REQUIRES: `self` is an Int sort.
        /// ENSURES: result sort is Int.
        #[kani_requires(self.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_int())]
        fn int_neg / try_int_neg,
        check: is_int,
        assert_msg: "int_neg requires Int sort",
        error_expected: "Int",
        variant: IntNeg
    }

    // ===== Integer Comparison Operations =====

    binop_to_bool! {
        /// Integer less than.
        /// REQUIRES: `self` and `other` are Int sorts.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_int() && other.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn int_lt / try_int_lt,
        check: int_same,
        assert_msg: "int_lt requires Int sorts",
        error_expected: "Int sorts",
        variant: IntLt
    }

    binop_to_bool! {
        /// Integer less than or equal.
        /// REQUIRES: `self` and `other` are Int sorts.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_int() && other.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn int_le / try_int_le,
        check: int_same,
        assert_msg: "int_le requires Int sorts",
        error_expected: "Int sorts",
        variant: IntLe
    }

    binop_to_bool! {
        /// Integer greater than.
        /// REQUIRES: `self` and `other` are Int sorts.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_int() && other.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn int_gt / try_int_gt,
        check: int_same,
        assert_msg: "int_gt requires Int sorts",
        error_expected: "Int sorts",
        variant: IntGt
    }

    binop_to_bool! {
        /// Integer greater than or equal.
        /// REQUIRES: `self` and `other` are Int sorts.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_int() && other.sort.is_int())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn int_ge / try_int_ge,
        check: int_same,
        assert_msg: "int_ge requires Int sorts",
        error_expected: "Int sorts",
        variant: IntGe
    }

    // ===== Sort Conversion Operations =====

    /// Convert integer to bitvector with truncation.
    /// REQUIRES: `self` is an Int sort.
    /// ENSURES: result sort is BitVec of the given width.
    ///
    /// The result is a bitvector with value (self mod 2^width).
    /// In SMT-LIB: ((_ int2bv w) i).
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Expr, Sort};
    ///
    /// // Convert an integer to a 32-bit bitvector
    /// let int_val = Expr::int_const(1000i32);
    /// let bv = int_val.int2bv(32);
    /// assert!(bv.sort().is_bitvec());
    /// assert_eq!(bv.sort().bitvec_width(), Some(32));
    /// ```
    ///
    /// # Panics
    /// Panics if `self` is not Int-sorted or `width == 0`. Only call this on
    /// terms whose sort is a locally-guaranteed invariant; for
    /// externally-sourced terms use [`Expr::try_int2bv`] and fail closed on
    /// the error.
    #[cfg_attr(kani, kani::requires(self.sort.is_int() && width > 0))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bitvec()))]
    #[must_use = "expression operations return a new Expr"]
    #[track_caller]
    pub fn int2bv(self, width: u32) -> Self {
        self.try_int2bv(width)
            .expect("int2bv requires Int sort with width > 0")
    }

    /// Fallible version of [`Expr::int2bv`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_int2bv(self, width: u32) -> Result<Self, crate::SortError> {
        if !self.sort.is_int() {
            return Err(crate::SortError::unary("int2bv", "Int", &self.sort));
        }
        if width == 0 {
            return Err(crate::SortError::Mismatch {
                operation: "int2bv",
                expected: "width > 0",
                actual: "0".to_string(),
            });
        }
        Ok(Self {
            sort: Sort::bitvec(width),
            value: Arc::new(ExprValue::Int2Bv(self, width)),
        })
    }
}
