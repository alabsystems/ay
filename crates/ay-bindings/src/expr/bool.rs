// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Boolean operations for AY expressions.

use crate::sort::Sort;
use std::sync::Arc;

use super::{Expr, ExprValue};

/// Predicate: both operands are Bool sorts.
fn bool_same(a: &Expr, b: &Expr) -> bool {
    a.sort.is_bool() && b.sort.is_bool()
}

impl Expr {
    // ===== Boolean Operations =====

    /// Logical NOT.
    /// REQUIRES: `self` is a Bool sort.
    /// ENSURES: result sort is Bool.
    #[cfg_attr(kani, kani::requires(self.sort.is_bool()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    #[must_use = "expression operations return a new Expr"]
    #[allow(clippy::should_implement_trait)] // Intentional SMT-LIB2 API naming, not std::ops::Not
    pub fn not(self) -> Self {
        self.try_not().expect("NOT requires Bool sort")
    }

    /// Logical AND (binary).
    /// REQUIRES: `self` and `other` are Bool sorts.
    /// ENSURES: result sort is Bool.
    #[cfg_attr(kani, kani::requires(self.sort.is_bool() && other.sort.is_bool()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn and(self, other: Self) -> Self {
        self.try_and(other).expect("AND requires Bool sorts")
    }

    /// Logical AND (n-ary).
    /// REQUIRES: every element is a Bool sort.
    /// ENSURES: result sort is Bool.
    #[cfg_attr(kani, kani::requires(exprs.iter().all(|e| e.sort.is_bool())))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn and_many(exprs: Vec<Self>) -> Self {
        Self::try_and_many(exprs).expect("AND requires all Bool sorts")
    }

    /// Logical OR (binary).
    /// REQUIRES: `self` and `other` are Bool sorts.
    /// ENSURES: result sort is Bool.
    #[cfg_attr(kani, kani::requires(self.sort.is_bool() && other.sort.is_bool()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn or(self, other: Self) -> Self {
        self.try_or(other).expect("OR requires Bool sorts")
    }

    /// Logical OR (n-ary).
    /// REQUIRES: every element is a Bool sort.
    /// ENSURES: result sort is Bool.
    #[cfg_attr(kani, kani::requires(exprs.iter().all(|e| e.sort.is_bool())))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn or_many(exprs: Vec<Self>) -> Self {
        Self::try_or_many(exprs).expect("OR requires all Bool sorts")
    }

    binop_to_bool! {
        /// Logical XOR.
        /// REQUIRES: `self` and `other` are Bool sorts.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_bool() && other.sort.is_bool())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn xor / try_xor,
        check: bool_same,
        assert_msg: "XOR requires Bool sorts",
        error_expected: "Bool",
        variant: Xor
    }

    binop_to_bool! {
        /// Logical implication.
        /// REQUIRES: `self` and `other` are Bool sorts.
        /// ENSURES: result sort is Bool.
        #[kani_requires(self.sort.is_bool() && other.sort.is_bool())]
        #[kani_ensures(|result: &Self| result.sort.is_bool())]
        fn implies / try_implies,
        check: bool_same,
        assert_msg: "IMPLIES requires Bool sorts",
        error_expected: "Bool",
        variant: Implies
    }

    /// Biconditional / logical equivalence (a <=> b).
    /// Equivalent to `self.eq(other)` when both are Bool, but validates both are Bool-sorted.
    /// REQUIRES: `self` and `other` are Bool sorts.
    /// ENSURES: result sort is Bool.
    #[cfg_attr(kani, kani::requires(self.sort.is_bool() && other.sort.is_bool()))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn iff(self, other: Self) -> Self {
        self.try_iff(other).expect("IFF requires Bool sorts")
    }

    /// If-then-else.
    /// REQUIRES: `cond` is Bool and `then_expr`/`else_expr` share a sort.
    /// ENSURES: result sort matches `then_expr`.
    #[cfg_attr(kani, kani::requires(cond.sort.is_bool() && then_expr.sort == else_expr.sort))]
    #[must_use = "expression operations return a new Expr"]
    pub fn ite(cond: Self, then_expr: Self, else_expr: Self) -> Self {
        Self::try_ite(cond, then_expr, else_expr)
            .expect("ITE requires Bool condition and matching branch sorts")
    }

    // ===== Equality and Comparison =====

    /// Equality.
    /// REQUIRES: `self` and `other` have identical sorts.
    /// ENSURES: result sort is Bool.
    #[cfg_attr(kani, kani::requires(self.sort == other.sort))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn eq(self, other: Self) -> Self {
        self.try_eq(other).expect("EQ requires same sort")
    }

    /// Not equal (convenience method).
    /// REQUIRES: `self` and `other` have identical sorts.
    /// ENSURES: result sort is Bool.
    #[cfg_attr(kani, kani::requires(self.sort == other.sort))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn ne(self, other: Self) -> Self {
        self.eq(other).not()
    }

    /// Distinct (n-ary not equal).
    /// REQUIRES: all expressions share the same sort (or list is empty).
    /// ENSURES: result sort is Bool.
    #[cfg_attr(kani, kani::requires(exprs.len() < 2 || exprs.iter().all(|e| e.sort == exprs[0].sort)))]
    #[cfg_attr(kani, kani::ensures(|result: &Self| result.sort.is_bool()))]
    #[must_use = "expression operations return a new Expr"]
    pub fn distinct(exprs: Vec<Self>) -> Self {
        Self::try_distinct(exprs).expect("DISTINCT requires all same sort")
    }

    // --- Fallible (try_) variants ---

    /// Fallible version of [`Expr::not`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_not(self) -> Result<Self, crate::SortError> {
        if !self.sort.is_bool() {
            return Err(crate::SortError::unary("not", "Bool", &self.sort));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::Not(self)),
        })
    }

    /// Fallible version of [`Expr::and`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_and(self, other: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_bool() || !other.sort.is_bool() {
            return Err(crate::SortError::binary(
                "and",
                "Bool",
                &self.sort,
                &other.sort,
            ));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::And(vec![self, other])),
        })
    }

    /// Fallible version of [`Expr::and_many`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_and_many(exprs: Vec<Self>) -> Result<Self, crate::SortError> {
        if let Some(bad) = exprs.iter().find(|e| !e.sort.is_bool()) {
            return Err(crate::SortError::unary("and_many", "all Bool", &bad.sort));
        }
        if exprs.is_empty() {
            return Ok(Self::true_());
        }
        if exprs.len() == 1 {
            return Ok(exprs
                .into_iter()
                .next()
                .expect("vec has exactly one element after length check"));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::And(exprs)),
        })
    }

    /// Fallible version of [`Expr::or`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_or(self, other: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_bool() || !other.sort.is_bool() {
            return Err(crate::SortError::binary(
                "or",
                "Bool",
                &self.sort,
                &other.sort,
            ));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::Or(vec![self, other])),
        })
    }

    /// Fallible version of [`Expr::or_many`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_or_many(exprs: Vec<Self>) -> Result<Self, crate::SortError> {
        if let Some(bad) = exprs.iter().find(|e| !e.sort.is_bool()) {
            return Err(crate::SortError::unary("or_many", "all Bool", &bad.sort));
        }
        if exprs.is_empty() {
            return Ok(Self::false_());
        }
        if exprs.len() == 1 {
            return Ok(exprs
                .into_iter()
                .next()
                .expect("vec has exactly one element after length check"));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::Or(exprs)),
        })
    }

    // try_xor and try_implies are generated by binop_to_bool! macros above.

    /// Fallible version of [`Expr::iff`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_iff(self, other: Self) -> Result<Self, crate::SortError> {
        if !self.sort.is_bool() || !other.sort.is_bool() {
            return Err(crate::SortError::binary(
                "iff",
                "Bool",
                &self.sort,
                &other.sort,
            ));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::Eq(self, other)),
        })
    }

    /// Fallible version of [`Expr::ite`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_ite(cond: Self, then_expr: Self, else_expr: Self) -> Result<Self, crate::SortError> {
        if !cond.sort.is_bool() {
            return Err(crate::SortError::unary(
                "ite (condition)",
                "Bool",
                &cond.sort,
            ));
        }
        if then_expr.sort != else_expr.sort {
            return Err(crate::SortError::binary(
                "ite (branches)",
                "matching sorts",
                &then_expr.sort,
                &else_expr.sort,
            ));
        }
        let result_sort = then_expr.sort.clone();
        Ok(Self {
            sort: result_sort,
            value: Arc::new(ExprValue::Ite {
                cond,
                then_expr,
                else_expr,
            }),
        })
    }

    /// Fallible version of [`Expr::eq`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_eq(self, other: Self) -> Result<Self, crate::SortError> {
        if self.sort != other.sort {
            return Err(crate::SortError::binary(
                "eq",
                "matching sorts",
                &self.sort,
                &other.sort,
            ));
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::Eq(self, other)),
        })
    }

    /// Fallible version of [`Expr::ne`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_ne(self, other: Self) -> Result<Self, crate::SortError> {
        let eq = self.try_eq(other)?;
        eq.try_not()
    }

    /// Fallible version of [`Expr::distinct`].
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_distinct(exprs: Vec<Self>) -> Result<Self, crate::SortError> {
        if exprs.len() >= 2 {
            let first_sort = &exprs[0].sort;
            if let Some(bad) = exprs.iter().find(|e| &e.sort != first_sort) {
                return Err(crate::SortError::binary(
                    "distinct",
                    "all same sort",
                    first_sort,
                    &bad.sort,
                ));
            }
        }
        Ok(Self {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::Distinct(exprs)),
        })
    }
}
