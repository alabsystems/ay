// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Core SMT command constructors for [`Constraint`].

use super::Constraint;
use crate::error::SortError;
use crate::expr::Expr;
use crate::sort::{DatatypeSort, Sort};

impl Constraint {
    /// Create a variable declaration.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn declare_const(name: impl Into<String>, sort: Sort) -> Self {
        Self::DeclareConst {
            name: name.into(),
            sort,
        }
    }

    /// Create a function declaration.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn declare_fun(name: impl Into<String>, arg_sorts: Vec<Sort>, return_sort: Sort) -> Self {
        Self::DeclareFun {
            name: name.into(),
            arg_sorts,
            return_sort,
        }
    }

    /// Create a non-recursive function definition.
    ///
    /// This emits SMT-LIB `(define-fun ...)`, which solvers can expand inline.
    /// Use it for transparent helper functions. Recursive or opaque functions
    /// should keep using `declare_fun` plus the appropriate axioms/encoding.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn define_fun(name: impl Into<String>, params: Vec<(String, Sort)>, body: Expr) -> Self {
        let return_sort = body.sort().clone();
        Self::DefineFun {
            name: name.into(),
            params,
            return_sort,
            body,
        }
    }

    /// Create a non-recursive function definition with an explicit return sort.
    ///
    /// Prefer [`define_fun`](Self::define_fun) when the body expression already
    /// carries the desired sort. This helper is useful at translation
    /// boundaries that need to check a declared return sort.
    ///
    /// # Panics
    ///
    /// Panics if `body.sort()` does not equal `return_sort`. Use
    /// [`try_define_fun_with_sort`](Self::try_define_fun_with_sort) for a
    /// fallible variant.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn define_fun_with_sort(
        name: impl Into<String>,
        params: Vec<(String, Sort)>,
        return_sort: Sort,
        body: Expr,
    ) -> Self {
        assert_eq!(
            body.sort(),
            &return_sort,
            "define_fun body sort must match return sort"
        );
        Self::DefineFun {
            name: name.into(),
            params,
            return_sort,
            body,
        }
    }

    /// Fallible non-recursive function definition with an explicit return sort.
    ///
    /// Returns `SortError` if `body.sort()` does not equal `return_sort`.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_define_fun_with_sort(
        name: impl Into<String>,
        params: Vec<(String, Sort)>,
        return_sort: Sort,
        body: Expr,
    ) -> Result<Self, SortError> {
        if body.sort() != &return_sort {
            return Err(SortError::unary(
                "define_fun",
                "body sort matching return sort",
                body.sort(),
            ));
        }
        Ok(Self::DefineFun {
            name: name.into(),
            params,
            return_sort,
            body,
        })
    }

    /// Create a datatype declaration.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn declare_datatype(datatype: DatatypeSort) -> Self {
        Self::DeclareDatatype(datatype)
    }

    /// Create an assertion.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn assert(expr: Expr) -> Self {
        assert!(expr.sort().is_bool(), "Assert requires Bool expression");
        Self::Assert { expr, label: None }
    }

    /// Fallible assertion — returns `SortError` if expr is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_assert(expr: Expr) -> Result<Self, SortError> {
        if !expr.sort().is_bool() {
            return Err(SortError::unary("assert", "Bool", expr.sort()));
        }
        Ok(Self::Assert { expr, label: None })
    }

    /// Create a labeled assertion.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn assert_labeled(expr: Expr, label: impl Into<String>) -> Self {
        assert!(expr.sort().is_bool(), "Assert requires Bool expression");
        Self::Assert {
            expr,
            label: Some(label.into()),
        }
    }

    /// Fallible labeled assertion — returns `SortError` if expr is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_assert_labeled(expr: Expr, label: impl Into<String>) -> Result<Self, SortError> {
        if !expr.sort().is_bool() {
            return Err(SortError::unary("assert_labeled", "Bool", expr.sort()));
        }
        Ok(Self::Assert {
            expr,
            label: Some(label.into()),
        })
    }

    /// Create an assumption (semantic alias for `assert`).
    ///
    /// In SMT-LIB2, both assertions and assumptions map to `(assert ...)`.
    /// This alias clarifies intent at call sites: use `assume` when adding
    /// path constraints or hypotheses, and `assert` when checking properties.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Constraint, Expr, Sort};
    ///
    /// // Assume x > 0 (path constraint)
    /// let x = Expr::var("x", Sort::int());
    /// let c = Constraint::assume(x.int_gt(Expr::int_const(0)));
    /// assert_eq!(c.to_string(), "(assert (> x 0))");
    /// ```
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn assume(expr: Expr) -> Self {
        Self::assert(expr)
    }

    /// Create a labeled assumption (semantic alias for `assert_labeled`).
    ///
    /// See [`Constraint::assume`] for semantics.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn assume_labeled(expr: Expr, label: impl Into<String>) -> Self {
        Self::assert_labeled(expr, label)
    }

    /// Create a soft assertion.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn soft_assert(expr: Expr, weight: u64) -> Self {
        assert!(expr.sort().is_bool(), "SoftAssert requires Bool expression");
        Self::SoftAssert {
            expr,
            weight,
            group: None,
        }
    }

    /// Create a soft assertion in a group.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn soft_assert_grouped(expr: Expr, weight: u64, group: impl Into<String>) -> Self {
        assert!(expr.sort().is_bool(), "SoftAssert requires Bool expression");
        Self::SoftAssert {
            expr,
            weight,
            group: Some(group.into()),
        }
    }

    /// Fallible soft assertion — returns `Err` if expr is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_soft_assert(expr: Expr, weight: u64) -> Result<Self, SortError> {
        if !expr.sort().is_bool() {
            return Err(SortError::unary("soft_assert", "Bool", expr.sort()));
        }
        Ok(Self::SoftAssert {
            expr,
            weight,
            group: None,
        })
    }

    /// Create a push command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn push() -> Self {
        Self::Push
    }

    /// Create a pop command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn pop(levels: u32) -> Self {
        Self::Pop(levels)
    }

    /// Create a check-sat command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn check_sat() -> Self {
        Self::CheckSat
    }

    /// Create a check-sat-assuming command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn check_sat_assuming(assumptions: Vec<Expr>) -> Self {
        for a in &assumptions {
            assert!(a.sort().is_bool(), "Assumptions must be Bool expressions");
        }
        Self::CheckSatAssuming(assumptions)
    }

    /// Fallible check-sat-assuming — returns `Err` if any assumption is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_check_sat_assuming(assumptions: Vec<Expr>) -> Result<Self, SortError> {
        for a in &assumptions {
            if !a.sort().is_bool() {
                return Err(SortError::unary(
                    "check_sat_assuming",
                    "Bool assumption",
                    a.sort(),
                ));
            }
        }
        Ok(Self::CheckSatAssuming(assumptions))
    }

    /// Create a get-model command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn get_model() -> Self {
        Self::GetModel
    }

    /// Create a get-value command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn get_value(exprs: Vec<Expr>) -> Self {
        Self::GetValue(exprs)
    }

    /// Create a get-unsat-core command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn get_unsat_core() -> Self {
        Self::GetUnsatCore
    }

    /// Create a set-option command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn set_option(name: impl Into<String>, value: impl Into<String>) -> Self {
        Self::SetOption {
            name: name.into(),
            value: value.into(),
        }
    }

    /// Create a set-logic command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn set_logic(logic: impl Into<String>) -> Self {
        Self::SetLogic(logic.into())
    }

    /// Create an exit command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn exit() -> Self {
        Self::Exit
    }
}
