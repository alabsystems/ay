// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Horn clause definitions

use crate::{ChcExpr, PredicateId};
use std::fmt;

/// Opaque identifier for a TLA+ action (disjunct of the Next relation).
///
/// In TLA+ model checking, the next-state relation is decomposed as
/// `Next = A1 \/ A2 \/ ... \/ An`, where each `Ai` is an action. This ID
/// tags transition clauses with their originating action so that PDR can
/// discover per-action invariants and produce action-aware counterexample traces.
///
/// `ActionId` values are meaningful only within the scope of the `ChcProblem`
/// that created them. They are dense indices suitable for use as vector offsets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ActionId(pub(crate) u32);

impl ActionId {
    /// Create a new action ID.
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw ID value as a `usize` index.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for ActionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Action{}", self.0)
    }
}

/// Body (antecedent) of a constrained Horn clause.
///
/// Semantically, this is a conjunction of:
/// - Zero or more predicate applications (uninterpreted relation calls), and
/// - An optional background-theory constraint (an interpreted [`ChcExpr`]).
///
/// The `constraint` is treated as `true` when it is `None`, so an empty
/// `ClauseBody` represents `true`.
///
/// This split is intentional: most CHC engines treat predicate applications
/// (control-flow / recursion) differently from the interpreted constraint
/// (data-flow in the background theory).
///
/// Invariants (by construction of a [`crate::ChcProblem`]):
/// - Every [`PredicateId`] refers to a predicate declared in the same problem.
/// - Each predicate application's argument count and sorts match the predicate
///   declaration (`Predicate.arg_sorts`).
/// - When present, `constraint` is a Boolean expression.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ClauseBody {
    /// Predicate applications: (predicate_id, arguments)
    pub predicates: Vec<(PredicateId, Vec<ChcExpr>)>,
    /// Constraint (background theory formula)
    pub constraint: Option<ChcExpr>,
}

impl ClauseBody {
    /// Create a body with predicates and a constraint
    pub fn new(predicates: Vec<(PredicateId, Vec<ChcExpr>)>, constraint: Option<ChcExpr>) -> Self {
        Self {
            predicates,
            constraint,
        }
    }

    /// Create a body with only a constraint (no predicate applications)
    pub fn constraint(c: ChcExpr) -> Self {
        Self {
            predicates: Vec::new(),
            constraint: Some(c),
        }
    }

    /// Create a body with only predicate applications
    pub fn predicates_only(predicates: Vec<(PredicateId, Vec<ChcExpr>)>) -> Self {
        Self {
            predicates,
            constraint: None,
        }
    }

    /// Create an empty body (represents "true")
    pub fn empty() -> Self {
        Self {
            predicates: Vec::new(),
            constraint: None,
        }
    }

    /// Check if the body is empty (true)
    pub fn is_empty(&self) -> bool {
        self.predicates.is_empty() && self.constraint.is_none()
    }

    /// Check if this is a fact (no predicates in body)
    pub fn is_fact(&self) -> bool {
        self.predicates.is_empty()
    }

    /// Get all variables in the body
    pub fn vars(&self) -> Vec<crate::ChcVar> {
        let mut result = Vec::new();
        for (_, args) in &self.predicates {
            for arg in args {
                for v in arg.vars() {
                    if !result.contains(&v) {
                        result.push(v);
                    }
                }
            }
        }
        if let Some(c) = &self.constraint {
            for v in c.vars() {
                if !result.contains(&v) {
                    result.push(v);
                }
            }
        }
        result
    }

    /// Iteratively tear down owned `ChcExpr` trees to avoid recursive Drop.
    pub(crate) fn iterative_drop(mut self) {
        for (_, args) in self.predicates.drain(..) {
            for arg in args {
                ChcExpr::iterative_drop(arg);
            }
        }
        if let Some(constraint) = self.constraint.take() {
            ChcExpr::iterative_drop(constraint);
        }
    }
}

impl fmt::Display for ClauseBody {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts = Vec::new();
        for (pred, args) in &self.predicates {
            let args_str: Vec<_> = args.iter().map(ToString::to_string).collect();
            parts.push(format!("{}({})", pred, args_str.join(", ")));
        }
        if let Some(c) = &self.constraint {
            parts.push(c.to_string());
        }
        if parts.is_empty() {
            write!(f, "true")
        } else {
            write!(f, "{}", parts.join(" /\\ "))
        }
    }
}

/// Head (consequent) of a constrained Horn clause.
///
/// A CHC head is either a predicate application (a derived fact) or `false`
/// (a safety query). Clauses with a `False` head assert that the body is
/// unreachable under a satisfying interpretation of predicates.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ClauseHead {
    /// Conclude a predicate application.
    Predicate(PredicateId, Vec<ChcExpr>),
    /// `false` (used for safety queries).
    False,
}

impl ClauseHead {
    /// Check if this is a query (head is false)
    pub fn is_query(&self) -> bool {
        matches!(self, Self::False)
    }

    /// Get the predicate ID if this is a predicate head
    pub fn predicate_id(&self) -> Option<PredicateId> {
        match self {
            Self::Predicate(id, _) => Some(*id),
            Self::False => None,
        }
    }

    /// Get all variables in the head
    pub fn vars(&self) -> Vec<crate::ChcVar> {
        match self {
            Self::Predicate(_, args) => {
                let mut result = Vec::new();
                for arg in args {
                    for v in arg.vars() {
                        if !result.contains(&v) {
                            result.push(v);
                        }
                    }
                }
                result
            }
            Self::False => Vec::new(),
        }
    }

    /// Iteratively tear down owned `ChcExpr` trees to avoid recursive Drop.
    pub(crate) fn iterative_drop(self) {
        if let Self::Predicate(_, args) = self {
            for arg in args {
                ChcExpr::iterative_drop(arg);
            }
        }
    }
}

impl fmt::Display for ClauseHead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Predicate(pred, args) => {
                let args_str: Vec<_> = args.iter().map(ToString::to_string).collect();
                write!(f, "{}({})", pred, args_str.join(", "))
            }
            Self::False => write!(f, "false"),
        }
    }
}

/// A constrained Horn clause (CHC).
///
/// This is the canonical `body => head` form used throughout the solver. In
/// typical SMT-LIB CHC encodings (e.g. `rule`/`query`), variables are
/// implicitly universally quantified; in this in-memory representation, all
/// variables appearing in `body` or `head` are treated as universally
/// quantified.
///
/// A clause is a *query* when `head` is [`ClauseHead::False`]. Intuitively, a
/// satisfying solution must make the body impossible (prove safety), since
/// `body => false` is equivalent to `¬body`.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct HornClause {
    /// Antecedent (`body`) of the implication.
    pub body: ClauseBody,
    /// Consequent (`head`) of the implication.
    pub head: ClauseHead,
    /// Optional TLA+ action identifier for per-action invariant discovery.
    ///
    /// When set, this clause represents a transition under a specific action
    /// in a TLA+ specification. PDR uses this to generate per-action blocking
    /// lemmas and produce action-annotated counterexample traces.
    pub action_id: Option<ActionId>,
}

impl HornClause {
    /// Create a new Horn clause
    pub fn new(body: ClauseBody, head: ClauseHead) -> Self {
        Self {
            body,
            head,
            action_id: None,
        }
    }

    /// Create a fact: constraint => P(args)
    pub fn fact(constraint: ChcExpr, pred: PredicateId, args: Vec<ChcExpr>) -> Self {
        Self {
            body: ClauseBody::constraint(constraint),
            head: ClauseHead::Predicate(pred, args),
            action_id: None,
        }
    }

    /// Create a query: body => false
    pub fn query(body: ClauseBody) -> Self {
        Self {
            body,
            head: ClauseHead::False,
            action_id: None,
        }
    }

    /// Tag this clause with an action identifier for per-action invariant discovery.
    pub fn with_action(mut self, action: ActionId) -> Self {
        self.action_id = Some(action);
        self
    }

    /// Check if this is a query clause
    pub fn is_query(&self) -> bool {
        self.head.is_query()
    }

    /// Check if this is a fact (no predicates in body)
    pub fn is_fact(&self) -> bool {
        self.body.is_fact()
    }

    /// Get all variables in the clause
    pub fn vars(&self) -> Vec<crate::ChcVar> {
        let mut result = self.body.vars();
        for v in self.head.vars() {
            if !result.contains(&v) {
                result.push(v);
            }
        }
        result
    }

    /// Get all predicate IDs used in the clause
    pub fn predicate_ids(&self) -> Vec<PredicateId> {
        let mut result: Vec<_> = self.body.predicates.iter().map(|(id, _)| *id).collect();
        if let Some(id) = self.head.predicate_id() {
            if !result.contains(&id) {
                result.push(id);
            }
        }
        result
    }

    /// Iteratively tear down owned body/head expressions to avoid recursive Drop.
    pub(crate) fn iterative_drop(self) {
        self.body.iterative_drop();
        self.head.iterative_drop();
    }
}

impl fmt::Display for HornClause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} => {}", self.body, self.head)
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
