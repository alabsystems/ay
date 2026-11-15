// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::Control;
use crate::expr::{MAX_EXPR_RECURSION_DEPTH, MAX_PREPROCESSING_NODES};
use crate::{ChcExpr, ChcProblem, ChcSort, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashSet;

#[derive(Clone, Copy)]
pub(super) enum Node<'a> {
    Expr(&'a ChcExpr, usize),
    Sort(&'a ChcSort, usize),
    Name(&'a str),
}

pub(super) struct Scan<'a, 'b> {
    control: &'a mut Control<'b>,
    remaining: usize,
    /// Expression nodes whose children have already been enqueued, by `Arc`
    /// address.
    ///
    /// `ChcExpr`'s children are `Arc`, so an expression is a DAG, and the
    /// substitution this walk admits keeps it one on purpose: `substitute.rs`
    /// carries a `*const Self` memo precisely "so the downstream
    /// eq/hash/drop/simplify walks stay linear too". Expanding a shared node
    /// once per incoming EDGE would undo exactly that sharing and unfold the
    /// DAG into its tree, which is both unbounded work and — because
    /// `remaining` would then be charged against tree nodes — a refusal on
    /// expressions the DAG never brings near the cap. That refusal is not
    /// recoverable: `ExactExpansionRefused` returns `Unknown` from `solve()`
    /// without the legacy fallback the neighbouring `Ok(None)` arm still takes.
    ///
    /// Deduplication is unobservable in the result. `check`/`check_all` visit
    /// with `|_| Some(())`, and the `variables` collector keys on variable name
    /// and rejects a conflicting sort, so re-walking an IDENTICAL `Arc` could
    /// only re-record what its first visit already recorded.
    expanded: DetHashSet<*const ChcExpr>,
}

impl<'a, 'b> Scan<'a, 'b> {
    pub(super) fn new(control: &'a mut Control<'b>) -> Self {
        Self {
            control,
            remaining: MAX_PREPROCESSING_NODES,
            expanded: DetHashSet::default(),
        }
    }

    #[cfg(test)]
    pub(super) fn with_limit(control: &'a mut Control<'b>, remaining: usize) -> Self {
        Self {
            control,
            remaining,
            expanded: DetHashSet::default(),
        }
    }

    fn push<'c>(&mut self, node: Node<'c>, pending: &mut Vec<Node<'c>>) -> Option<()> {
        self.control.poll()?;
        if self.remaining == 0
            || matches!(node, Node::Expr(_, depth) | Node::Sort(_, depth)
                if depth >= MAX_EXPR_RECURSION_DEPTH)
        {
            return self.control.refuse();
        }
        self.remaining -= 1;
        pending.push(node);
        Some(())
    }

    fn walk<'c>(
        &mut self,
        root: Node<'c>,
        visit: &mut impl FnMut(Node<'c>) -> Option<()>,
    ) -> Option<()> {
        let mut pending = Vec::new();
        self.push(root, &mut pending)?;
        while let Some(node) = pending.pop() {
            self.control.poll()?;
            if visit(node).is_none() {
                return self.control.refuse();
            }
            match node {
                Node::Expr(expression, depth) => {
                    // Every edge is still pushed, polled, charged against
                    // `remaining` and depth-checked exactly as before, so no
                    // refusal this walk used to make is lost. Only the repeated
                    // EXPANSION of an already-enqueued node is skipped, which
                    // is what keeps the walk linear in the DAG.
                    if self.expanded.insert(std::ptr::from_ref(expression)) {
                        self.expression_children(expression, depth, &mut pending)?;
                    }
                }
                Node::Sort(sort, depth) => self.sort_children(sort, depth, &mut pending)?,
                Node::Name(_) => {}
            }
        }
        Some(())
    }

    fn expression_children<'c>(
        &mut self,
        expression: &'c ChcExpr,
        depth: usize,
        pending: &mut Vec<Node<'c>>,
    ) -> Option<()> {
        let children = match expression {
            ChcExpr::ArrayLambda(lambda) => {
                for formal in std::iter::once(lambda.binder()).chain(lambda.formals()) {
                    self.push(Node::Name(&formal.name), pending)?;
                    self.push(Node::Sort(&formal.sort, 0), pending)?;
                }
                self.push(Node::Expr(lambda.body(), depth + 1), pending)?;
                lambda.captures()
            }
            ChcExpr::Op(_, args) => args.as_slice(),
            ChcExpr::PredicateApp(name, _, args) => {
                self.push(Node::Name(name), pending)?;
                args
            }
            ChcExpr::FuncApp(name, sort, args) => {
                self.push(Node::Name(name), pending)?;
                self.push(Node::Sort(sort, 0), pending)?;
                args
            }
            ChcExpr::ConstArray(sort, value) => {
                self.push(Node::Sort(sort, 0), pending)?;
                std::slice::from_ref(value)
            }
            ChcExpr::Var(var) => {
                self.push(Node::Name(&var.name), pending)?;
                self.push(Node::Sort(&var.sort, 0), pending)?;
                &[]
            }
            ChcExpr::ConstArrayMarker(sort) => {
                self.push(Node::Sort(sort, 0), pending)?;
                &[]
            }
            ChcExpr::IsTesterMarker(name) => {
                self.push(Node::Name(name), pending)?;
                &[]
            }
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => &[],
        };
        for child in children.iter().rev() {
            self.push(Node::Expr(child, depth + 1), pending)?;
        }
        Some(())
    }

    fn sort_children<'c>(
        &mut self,
        sort: &'c ChcSort,
        depth: usize,
        pending: &mut Vec<Node<'c>>,
    ) -> Option<()> {
        match sort {
            ChcSort::Array(key, value) => {
                self.push(Node::Sort(value, depth + 1), pending)?;
                self.push(Node::Sort(key, depth + 1), pending)?;
            }
            ChcSort::Datatype { name, constructors } => {
                self.push(Node::Name(name), pending)?;
                for constructor in constructors.iter() {
                    self.push(Node::Name(&constructor.name), pending)?;
                    for selector in &constructor.selectors {
                        self.push(Node::Name(&selector.name), pending)?;
                        self.push(Node::Sort(&selector.sort, depth + 1), pending)?;
                    }
                }
            }
            ChcSort::Uninterpreted(name) => self.push(Node::Name(name), pending)?,
            ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {}
        }
        Some(())
    }

    pub(super) fn expression<'c>(
        &mut self,
        expression: &'c ChcExpr,
        visit: &mut impl FnMut(Node<'c>) -> Option<()>,
    ) -> Option<()> {
        self.walk(Node::Expr(expression, 0), visit)
    }

    pub(super) fn conjunction(&mut self, expressions: &[ChcExpr]) -> Option<()> {
        // Reserve the enclosing conjunction node used by the exact simplifier.
        self.remaining = self.remaining.checked_sub(1)?;
        for expression in expressions {
            self.walk(Node::Expr(expression, 1), &mut |_| Some(()))?;
        }
        Some(())
    }

    pub(super) fn clause<'c>(
        &mut self,
        clause: &'c HornClause,
        visit: &mut impl FnMut(Node<'c>) -> Option<()>,
    ) -> Option<()> {
        self.control.poll()?;
        for (_, args) in &clause.body.predicates {
            for argument in args {
                self.expression(argument, visit)?;
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            self.expression(constraint, visit)?;
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for argument in args {
                self.expression(argument, visit)?;
            }
        }
        Some(())
    }

    pub(super) fn problem<'c>(
        &mut self,
        problem: &'c ChcProblem,
        visit: &mut impl FnMut(Node<'c>) -> Option<()>,
    ) -> Option<()> {
        for predicate in problem.predicates() {
            self.walk(Node::Name(&predicate.name), visit)?;
            for sort in &predicate.arg_sorts {
                self.walk(Node::Sort(sort, 0), visit)?;
            }
        }
        for (name, constructors) in problem.datatype_defs() {
            self.walk(Node::Name(name), visit)?;
            for (constructor, selectors) in constructors {
                self.walk(Node::Name(constructor), visit)?;
                for (selector, sort) in selectors {
                    self.walk(Node::Name(selector), visit)?;
                    self.walk(Node::Sort(sort, 0), visit)?;
                }
            }
        }
        for name in problem.action_names() {
            self.walk(Node::Name(name), visit)?;
        }
        for clause in problem.source_clauses() {
            self.clause(clause, visit)?;
        }
        Some(())
    }
}
