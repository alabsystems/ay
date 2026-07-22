// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! AYProgram Horn clause (CHC) methods — relations, rules, queries.

use super::AYProgram;
use crate::constraint::Constraint;
use crate::error::SortError;
use crate::expr::Expr;
use crate::sort::Sort;

impl AYProgram {
    /// Declare a relation (predicate symbol) for CHC solving.
    ///
    /// Relations are the building blocks of Horn clause problems.
    /// Each relation has a name and a list of argument sorts.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Sort, AYProgram};
    ///
    /// let mut program = AYProgram::horn();
    /// // Declare Inv(x: Int, y: Int)
    /// program.declare_rel("Inv", vec![Sort::int(), Sort::int()]);
    /// ```
    pub fn declare_rel(&mut self, name: impl Into<String>, arg_sorts: Vec<Sort>) {
        let name = name.into();
        self.declared_rels.push((name.clone(), arg_sorts.clone()));
        self.commands.push(Constraint::declare_rel(name, arg_sorts));
    }

    /// Declare an implicitly universally quantified variable for CHC rules.
    ///
    /// Variables declared with declare-var can be used in Horn clause rules
    /// without explicit quantification. This is Z3's extension for CHC.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Sort, AYProgram};
    ///
    /// let mut program = AYProgram::horn();
    /// // Declare universally quantified variable x
    /// program.declare_var("x", Sort::int());
    /// ```
    pub fn declare_var(&mut self, name: impl Into<String>, sort: Sort) {
        let name = name.into();
        self.declared_chc_vars.push((name.clone(), sort.clone()));
        self.commands.push(Constraint::declare_var(name, sort));
    }

    /// Add a Horn clause rule: body => head.
    ///
    /// A rule states that when the body holds, the head relation is reachable.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Expr, Sort, AYProgram};
    ///
    /// let mut program = AYProgram::horn();
    /// program.declare_rel("Inv", vec![]);
    /// // Rule: x < 10 => Inv
    /// let inv = Expr::var("Inv", Sort::bool());
    /// let x = Expr::var("x", Sort::int());
    /// let body_constraint = x.int_lt(Expr::int_const(10i32));
    /// program.rule(inv, body_constraint);
    /// ```
    pub fn rule(&mut self, head: Expr, body: Expr) {
        self.commands.push(Constraint::rule(head, body));
    }

    /// Add a Horn clause fact (unconditionally true).
    ///
    /// A fact states that a relation is always reachable (initial state).
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Expr, Sort, AYProgram};
    ///
    /// let mut program = AYProgram::horn();
    /// // Fact: Init(0, 0) is always true
    /// program.declare_rel("Init", vec![]);
    /// let init_expr = Expr::var("Init", Sort::bool());
    /// program.fact(init_expr);
    /// ```
    pub fn fact(&mut self, head: Expr) {
        self.commands.push(Constraint::fact(head));
    }

    /// Add a Horn clause constraint (no head).
    ///
    /// A constraint specifies states that should be unreachable.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Expr, Sort, AYProgram};
    ///
    /// let mut program = AYProgram::horn();
    /// // Constraint: Error(x) must be unreachable
    /// program.declare_rel("Error", vec![]);
    /// let error_expr = Expr::var("Error", Sort::bool());
    /// program.rule_constraint(error_expr);
    /// ```
    pub fn rule_constraint(&mut self, body: Expr) {
        self.commands.push(Constraint::rule_constraint(body));
    }

    /// Add a CHC query.
    ///
    /// Queries whether a relation is reachable (SAT) or unreachable (UNSAT).
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Expr, Sort, AYProgram};
    ///
    /// let mut program = AYProgram::horn();
    /// // Query: is Error reachable?
    /// program.declare_rel("Error", vec![]);
    /// let error_expr = Expr::var("Error", Sort::bool());
    /// program.query(error_expr);
    /// ```
    pub fn query(&mut self, rel: Expr) {
        self.commands.push(Constraint::query(rel));
    }

    // ===== Fallible CHC try_* variants =====

    /// Fallible Horn clause rule — returns `Err` if head or body is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_rule(&mut self, head: Expr, body: Expr) -> Result<(), SortError> {
        self.commands.push(Constraint::try_rule(head, body)?);
        Ok(())
    }

    /// Fallible Horn clause fact — returns `Err` if head is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fact(&mut self, head: Expr) -> Result<(), SortError> {
        self.commands.push(Constraint::try_fact(head)?);
        Ok(())
    }

    /// Fallible Horn clause constraint — returns `Err` if body is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_rule_constraint(&mut self, body: Expr) -> Result<(), SortError> {
        self.commands.push(Constraint::try_rule_constraint(body)?);
        Ok(())
    }

    /// Fallible CHC query — returns `Err` if rel is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_query(&mut self, rel: Expr) -> Result<(), SortError> {
        self.commands.push(Constraint::try_query(rel)?);
        Ok(())
    }
}
