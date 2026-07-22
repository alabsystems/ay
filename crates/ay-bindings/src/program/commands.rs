// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! AYProgram command emission — assertions, solve, push/pop, optimization.

use super::AYProgram;
use crate::constraint::Constraint;
use crate::error::SortError;
use crate::expr::Expr;

impl AYProgram {
    /// Add an assertion.
    pub fn assert(&mut self, expr: Expr) {
        self.commands.push(Constraint::assert(expr));
    }

    /// Add a labeled assertion.
    pub fn assert_labeled(&mut self, expr: Expr, label: impl Into<String>) {
        self.commands.push(Constraint::assert_labeled(expr, label));
    }

    /// Add multiple assertions.
    pub fn assert_all(&mut self, exprs: impl IntoIterator<Item = Expr>) {
        for expr in exprs {
            self.assert(expr);
        }
    }

    /// Add an assumption (semantic alias for `assert`).
    ///
    /// In SMT-LIB2, both assertions and assumptions map to `(assert ...)`.
    /// This alias clarifies intent at call sites: use `assume` when adding
    /// path constraints or hypotheses, and `assert` when checking properties.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Expr, Sort, AYProgram};
    ///
    /// let mut program = AYProgram::qf_bv();
    /// let x = program.declare_const("x", Sort::bv32());
    /// // Assume x > 0 (path constraint)
    /// let zero = Expr::bitvec_const(0i32, 32);
    /// program.assume(x.bvugt(zero));
    /// ```
    pub fn assume(&mut self, expr: Expr) {
        self.assert(expr);
    }

    /// Add a labeled assumption (semantic alias for `assert_labeled`).
    ///
    /// See [`AYProgram::assume`] for semantics.
    pub fn assume_labeled(&mut self, expr: Expr, label: impl Into<String>) {
        self.assert_labeled(expr, label);
    }

    /// Add a soft assertion.
    pub fn soft_assert(&mut self, expr: Expr, weight: u64) {
        self.commands.push(Constraint::soft_assert(expr, weight));
    }

    /// Push a context level.
    pub fn push(&mut self) {
        self.context_level += 1;
        self.commands.push(Constraint::push());
    }

    /// Pop context levels.
    pub fn pop(&mut self, levels: u32) {
        assert!(
            levels <= self.context_level,
            "Cannot pop {} levels when context level is {}",
            levels,
            self.context_level
        );
        self.context_level -= levels;
        self.commands.push(Constraint::pop(levels));
    }

    /// Fallible pop — returns `Err` if levels exceeds the current context level.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_pop(&mut self, levels: u32) -> Result<(), SortError> {
        if levels > self.context_level {
            return Err(SortError::StackUnderflow {
                operation: "pop",
                requested: levels,
                available: self.context_level,
            });
        }
        self.context_level -= levels;
        self.commands.push(Constraint::pop(levels));
        Ok(())
    }

    /// Add check-sat command.
    pub fn check_sat(&mut self) {
        self.commands.push(Constraint::check_sat());
    }

    /// Add check-sat-assuming command.
    pub fn check_sat_assuming(&mut self, assumptions: Vec<Expr>) {
        self.commands
            .push(Constraint::check_sat_assuming(assumptions));
    }

    /// Add get-model command.
    pub fn get_model(&mut self) {
        self.commands.push(Constraint::get_model());
    }

    /// Add get-value command.
    pub fn get_value(&mut self, exprs: Vec<Expr>) {
        self.commands.push(Constraint::get_value(exprs));
    }

    /// Add get-unsat-core command.
    pub fn get_unsat_core(&mut self) {
        self.commands.push(Constraint::get_unsat_core());
    }

    /// Add exit command.
    pub fn exit(&mut self) {
        self.commands.push(Constraint::exit());
    }

    /// Add a maximize objective.
    ///
    /// The expression must be of Int or Real sort. Multiple objectives
    /// are optimized lexicographically in declaration order.
    pub fn maximize(&mut self, expr: Expr) {
        self.commands.push(Constraint::maximize(expr));
    }

    /// Add a minimize objective.
    ///
    /// The expression must be of Int or Real sort. Multiple objectives
    /// are optimized lexicographically in declaration order.
    pub fn minimize(&mut self, expr: Expr) {
        self.commands.push(Constraint::minimize(expr));
    }

    /// Add get-objectives command to retrieve optimal values.
    pub fn get_objectives(&mut self) {
        self.commands.push(Constraint::get_objectives());
    }

    // ===== Fallible try_* variants (#5818, #3543) =====

    /// Fallible assertion — returns `Err` if expr is not Bool (#3543).
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_assert(&mut self, expr: Expr) -> Result<(), SortError> {
        self.commands.push(Constraint::try_assert(expr)?);
        Ok(())
    }

    /// Fallible labeled assertion — returns `Err` if expr is not Bool (#3543).
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_assert_labeled(
        &mut self,
        expr: Expr,
        label: impl Into<String>,
    ) -> Result<(), SortError> {
        self.commands
            .push(Constraint::try_assert_labeled(expr, label)?);
        Ok(())
    }

    /// Fallible soft assertion — returns `Err` if expr is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_soft_assert(&mut self, expr: Expr, weight: u64) -> Result<(), SortError> {
        self.commands
            .push(Constraint::try_soft_assert(expr, weight)?);
        Ok(())
    }

    /// Fallible check-sat-assuming — returns `Err` if any assumption is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_check_sat_assuming(&mut self, assumptions: Vec<Expr>) -> Result<(), SortError> {
        self.commands
            .push(Constraint::try_check_sat_assuming(assumptions)?);
        Ok(())
    }

    /// Fallible maximize — returns `Err` if expr is not Int or Real.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_maximize(&mut self, expr: Expr) -> Result<(), SortError> {
        self.commands.push(Constraint::try_maximize(expr)?);
        Ok(())
    }

    /// Fallible minimize — returns `Err` if expr is not Int or Real.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_minimize(&mut self, expr: Expr) -> Result<(), SortError> {
        self.commands.push(Constraint::try_minimize(expr)?);
        Ok(())
    }

    /// Add a raw constraint (used by execute_direct feature).
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.commands.push(constraint);
    }
}
