// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! CHC (Constrained Horn Clause) constructors for [`Constraint`].

use super::Constraint;
use crate::error::SortError;
use crate::expr::Expr;
use crate::sort::Sort;

impl Constraint {
    /// Create a relation declaration for CHC solving.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Constraint, Sort};
    ///
    /// // Declare a relation Inv(x: Int, y: Int)
    /// let decl = Constraint::declare_rel("Inv", vec![Sort::int(), Sort::int()]);
    /// assert_eq!(decl.to_string(), "(declare-rel Inv (Int Int))");
    /// ```
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn declare_rel(name: impl Into<String>, arg_sorts: Vec<Sort>) -> Self {
        Self::DeclareRel {
            name: name.into(),
            arg_sorts,
        }
    }

    /// Create a Horn clause rule: body => head.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Constraint, Expr, Sort};
    ///
    /// // Rule: true => Inv
    /// // Note: relation applications represented as Bool vars for SMT-LIB serialization
    /// let inv = Expr::var("Inv", Sort::bool());
    /// let rule = Constraint::rule(inv, Expr::bool_const(true));
    /// ```
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn rule(head: Expr, body: Expr) -> Self {
        assert!(
            head.sort().is_bool(),
            "Rule head must be Bool (relation application)"
        );
        assert!(body.sort().is_bool(), "Rule body must be Bool");
        Self::Rule {
            head: Some(head),
            body,
        }
    }

    /// Create a Horn clause fact (unconditional rule).
    ///
    /// A fact is a rule with `true` as the body, meaning the head
    /// is always reachable.
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Constraint, Expr, Sort};
    ///
    /// // Fact: Init(0) is always true
    /// // Note: relation applications represented as Bool vars for SMT-LIB serialization
    /// let init_0 = Expr::var("Init_0", Sort::bool());
    /// let fact = Constraint::fact(init_0);
    /// ```
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn fact(head: Expr) -> Self {
        assert!(
            head.sort().is_bool(),
            "Fact head must be Bool (relation application)"
        );
        Self::Rule {
            head: Some(head),
            body: Expr::bool_const(true),
        }
    }

    /// Create a Horn clause constraint (no head).
    ///
    /// A constraint rule asserts that the body cannot be satisfied
    /// (used for specifying what states should be unreachable).
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Constraint, Expr, Sort};
    ///
    /// // Constraint: Error(x) must be unreachable
    /// // Note: relation applications represented as Bool vars for SMT-LIB serialization
    /// let error_x = Expr::var("Error_x", Sort::bool());
    /// let constraint = Constraint::rule_constraint(error_x);
    /// ```
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn rule_constraint(body: Expr) -> Self {
        assert!(body.sort().is_bool(), "Rule constraint body must be Bool");
        Self::Rule { head: None, body }
    }

    /// Create a CHC query.
    ///
    /// Queries whether a relation is reachable (SAT) or unreachable (UNSAT).
    ///
    /// # Example
    /// ```rust
    /// use ay_bindings::{Constraint, Expr, Sort};
    ///
    /// // Query: is Error reachable?
    /// // Note: relation applications represented as Bool vars for SMT-LIB serialization
    /// let error = Expr::var("Error", Sort::bool());
    /// let query = Constraint::query(error);
    /// ```
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn query(rel: Expr) -> Self {
        assert!(
            rel.sort().is_bool(),
            "Query must be Bool (relation application)"
        );
        Self::Query(rel)
    }

    /// Declare an implicitly universally quantified variable for CHC rules.
    ///
    /// Variables declared with declare-var can be used in Horn clause rules
    /// without explicit quantification. This is Z3's extension for CHC.
    #[must_use = "constraints must be added to a program to take effect"]
    pub fn declare_var(name: impl Into<String>, sort: Sort) -> Self {
        Self::DeclareVar {
            name: name.into(),
            sort,
        }
    }

    /// Fallible Horn clause rule — returns `Err` if head or body is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_rule(head: Expr, body: Expr) -> Result<Self, SortError> {
        if !head.sort().is_bool() {
            return Err(SortError::unary("rule", "Bool head", head.sort()));
        }
        if !body.sort().is_bool() {
            return Err(SortError::unary("rule", "Bool body", body.sort()));
        }
        Ok(Self::Rule {
            head: Some(head),
            body,
        })
    }

    /// Fallible Horn clause fact — returns `Err` if head is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_fact(head: Expr) -> Result<Self, SortError> {
        if !head.sort().is_bool() {
            return Err(SortError::unary("fact", "Bool head", head.sort()));
        }
        Ok(Self::Rule {
            head: Some(head),
            body: Expr::bool_const(true),
        })
    }

    /// Fallible Horn clause constraint — returns `Err` if body is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_rule_constraint(body: Expr) -> Result<Self, SortError> {
        if !body.sort().is_bool() {
            return Err(SortError::unary(
                "rule_constraint",
                "Bool body",
                body.sort(),
            ));
        }
        Ok(Self::Rule { head: None, body })
    }

    /// Fallible CHC query — returns `Err` if rel is not Bool.
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_query(rel: Expr) -> Result<Self, SortError> {
        if !rel.sort().is_bool() {
            return Err(SortError::unary("query", "Bool relation", rel.sort()));
        }
        Ok(Self::Query(rel))
    }
}
