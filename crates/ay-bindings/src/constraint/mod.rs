// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! AY Constraint types.
//!
//! Constraints are the fundamental building blocks of verification problems.
//! They represent conditions that must hold (assertions) or can be assumed
//! (assumptions).
//!
//! ## Constraint Types
//!
//! - **Assert**: A condition that must be proven to hold.
//! - **Assume**: A condition that can be assumed true (hypothesis).
//! - **SoftAssert**: An optimization goal (for MaxSAT-like problems).
//!
//! ## SMT-LIB2 Mapping
//!
//! | Constraint | SMT-LIB2 |
//! |------------|----------|
//! | Assert(e) | (assert e) |
//! | Assume(e) | (assert e) ; assumptions become assertions |
//! | DefineFun | (define-fun name ((arg sort) ...) return body) |
//! | CheckSat | (check-sat) |

use crate::expr::Expr;
use crate::sort::{DatatypeSort, Sort};

mod chc;
mod core;
mod display;
pub mod logic;
mod optimization;

#[cfg(test)]
mod tests;

/// A constraint in a verification problem.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum Constraint {
    /// Variable declaration: (declare-const name sort).
    DeclareConst { name: String, sort: Sort },

    /// Function declaration: (declare-fun name (arg_sorts) return_sort).
    DeclareFun {
        name: String,
        arg_sorts: Vec<Sort>,
        return_sort: Sort,
    },

    /// Non-recursive function definition: (define-fun name ((arg sort) ...) return_sort body).
    DefineFun {
        name: String,
        params: Vec<(String, Sort)>,
        return_sort: Sort,
        body: Expr,
    },

    /// Datatype declaration: (declare-datatype name ((constructor (field sort) ...))).
    DeclareDatatype(DatatypeSort),

    /// Assert: (assert expr).
    ///
    /// The expression must be proven true by the solver.
    Assert {
        expr: Expr,
        /// Optional name/label for the assertion (for tracking counterexamples).
        label: Option<String>,
    },

    /// Soft assertion with weight (for optimization).
    SoftAssert {
        expr: Expr,
        weight: u64,
        group: Option<String>,
    },

    /// Push a context level.
    Push,

    /// Pop context levels.
    Pop(u32),

    /// Check satisfiability.
    CheckSat,

    /// Check satisfiability under assumptions.
    CheckSatAssuming(Vec<Expr>),

    /// Get model (after SAT).
    GetModel,

    /// Get value of expressions (after SAT).
    GetValue(Vec<Expr>),

    /// Get unsat core (after UNSAT with named assertions).
    GetUnsatCore,

    /// Set solver option.
    SetOption { name: String, value: String },

    /// Set logic (e.g., QF_BV, QF_AUFBV).
    SetLogic(String),

    /// Exit the solver.
    Exit,

    // --- CHC / Horn clause commands (Phase 3) ---
    /// Declare a relation (predicate symbol) for CHC solving.
    /// SMT-LIB syntax: (declare-rel name (sort1 sort2 ...))
    DeclareRel { name: String, arg_sorts: Vec<Sort> },

    /// Add a Horn clause rule.
    /// SMT-LIB syntax: (rule body) or (rule (=> body head))
    ///
    /// A Horn clause has the form: body => head
    /// - `head` is an application of a declared relation (None for a fact)
    /// - `body` is a conjunction of relation applications and constraints
    ///
    /// For facts (unconditionally true): head with empty body
    /// For rules: body implies head
    Rule {
        /// The head relation application (what the rule proves).
        /// If None, the body is asserted as a constraint.
        head: Option<Expr>,
        /// The body constraint(s) that must hold for the head to be reachable.
        body: Expr,
    },

    /// Query whether a relation is reachable (satisfiable in CHC sense).
    /// SMT-LIB syntax: (query rel) or (query (rel args...))
    ///
    /// Returns SAT if the queried relation is reachable under the rules,
    /// UNSAT if it's unreachable (safe).
    Query(Expr),

    /// Declare an implicitly universally quantified variable for CHC rules.
    /// SMT-LIB syntax: (declare-var name sort)
    ///
    /// Variables declared with declare-var can be used in rules without
    /// explicit quantification.
    DeclareVar { name: String, sort: Sort },

    // --- OMT (Optimization Modulo Theories) commands ---
    /// Maximize an objective expression.
    /// SMT-LIB syntax: (maximize expr)
    Maximize(Expr),

    /// Minimize an objective expression.
    /// SMT-LIB syntax: (minimize expr)
    Minimize(Expr),

    /// Get objective values after optimization.
    /// SMT-LIB syntax: (get-objectives)
    GetObjectives,
}
