// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! OMT (Optimization Modulo Theories) constructors for [`Constraint`].

use super::Constraint;
use crate::error::SortError;
use crate::expr::Expr;

impl Constraint {
    /// Create a maximize objective.
    ///
    /// The expression must be of Int or Real sort.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn maximize(expr: Expr) -> Self {
        assert!(
            expr.sort().is_int() || expr.sort().is_real(),
            "maximize requires Int or Real expression"
        );
        Self::Maximize(expr)
    }

    /// Create a minimize objective.
    ///
    /// The expression must be of Int or Real sort.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn minimize(expr: Expr) -> Self {
        assert!(
            expr.sort().is_int() || expr.sort().is_real(),
            "minimize requires Int or Real expression"
        );
        Self::Minimize(expr)
    }

    /// Create a get-objectives command.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn get_objectives() -> Self {
        Self::GetObjectives
    }

    /// Fallible maximize — returns `Err` if expr is not Int or Real.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_maximize(expr: Expr) -> Result<Self, SortError> {
        if !expr.sort().is_int() && !expr.sort().is_real() {
            return Err(SortError::unary("maximize", "Int or Real", expr.sort()));
        }
        Ok(Self::Maximize(expr))
    }

    /// Fallible minimize — returns `Err` if expr is not Int or Real.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_minimize(expr: Expr) -> Result<Self, SortError> {
        if !expr.sort().is_int() && !expr.sort().is_real() {
            return Err(SortError::unary("minimize", "Int or Real", expr.sort()));
        }
        Ok(Self::Minimize(expr))
    }
}
