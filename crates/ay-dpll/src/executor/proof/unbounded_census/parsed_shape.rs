// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #unbounded-population. The parsed-AST walk behind
//! [`super::ParsedRootShape`] — what one authored root really looks like when
//! no bound stops the measurement.

use ay_frontend::command::{Sort as FrontendSort, Term as FrontendTerm};
use ay_frontend::SExpr;

use super::ParsedRootShape;

/// One item of the walk's work list: the node, its depth, and — for terms —
/// the `let` nesting it sits under.
enum Node<'a> {
    Term(&'a FrontendTerm, u32, u32),
    Sort(&'a FrontendSort, u32),
    SExpr(&'a SExpr, u32),
}

/// Walk one parsed root to the end and report its shape.
#[must_use]
pub(in crate::executor) fn parsed_root_shape(root: &FrontendTerm) -> ParsedRootShape {
    let mut shape = ParsedRootShape::default();
    let mut pending = vec![Node::Term(root, 0, 0)];
    while let Some(node) = pending.pop() {
        shape.nodes = shape.nodes.saturating_add(1);
        match node {
            Node::Term(term, depth, let_depth) => {
                shape.depth = shape.depth.max(depth);
                shape.let_depth = shape.let_depth.max(let_depth);
                let next = depth.saturating_add(1);
                match term {
                    FrontendTerm::Const(_) | FrontendTerm::Symbol(_) => {
                        shape.bytes = shape.bytes.saturating_add(8);
                    }
                    FrontendTerm::App(op, args) | FrontendTerm::IndexedApp(op, _, args) => {
                        shape.bytes = shape
                            .bytes
                            .saturating_add(op.len() as u64)
                            .saturating_add(args.len() as u64 + 2);
                        pending.extend(args.iter().map(|a| Node::Term(a, next, let_depth)));
                    }
                    FrontendTerm::QualifiedApp(_, sort, args) => {
                        shape.bytes = shape.bytes.saturating_add(args.len() as u64 + 7);
                        pending.extend(args.iter().map(|a| Node::Term(a, next, let_depth)));
                        pending.push(Node::Sort(sort, next));
                    }
                    FrontendTerm::Let(bindings, body) => {
                        shape.let_bindings =
                            shape.let_bindings.saturating_add(bindings.len() as u32);
                        let inner = let_depth.saturating_add(1);
                        shape.bytes = shape.bytes.saturating_add(7);
                        pending.push(Node::Term(body, next, inner));
                        for (name, value) in bindings {
                            shape.bytes = shape.bytes.saturating_add(name.len() as u64 + 3);
                            pending.push(Node::Term(value, next, let_depth));
                        }
                    }
                    FrontendTerm::Forall(bindings, body)
                    | FrontendTerm::Exists(bindings, body)
                    | FrontendTerm::Lambda(bindings, body) => {
                        shape.binders = shape.binders.saturating_add(1);
                        shape.bytes = shape.bytes.saturating_add(10);
                        pending.push(Node::Term(body, next, let_depth));
                        for (name, sort) in bindings {
                            shape.bytes = shape.bytes.saturating_add(name.len() as u64 + 3);
                            pending.push(Node::Sort(sort, next));
                        }
                    }
                    FrontendTerm::Match(scrutinee, cases) => {
                        shape.bytes = shape.bytes.saturating_add(10);
                        pending.push(Node::Term(scrutinee, next, let_depth));
                        for (_, body) in cases {
                            pending.push(Node::Term(body, next, let_depth));
                        }
                    }
                    FrontendTerm::Annotated(body, annotations) => {
                        pending.push(Node::Term(body, next, let_depth));
                        for (name, value) in annotations {
                            shape.bytes = shape.bytes.saturating_add(name.len() as u64 + 1);
                            pending.push(Node::SExpr(value, next));
                        }
                    }
                    _ => shape.unpriced = shape.unpriced.saturating_add(1),
                }
            }
            Node::Sort(sort, depth) => {
                shape.depth = shape.depth.max(depth);
                walk_sort(sort, depth, &mut shape, &mut pending);
            }
            Node::SExpr(sexpr, depth) => {
                shape.depth = shape.depth.max(depth);
                walk_sexpr(sexpr, depth, &mut shape, &mut pending);
            }
        }
    }
    shape
}

/// Price one parsed sort and queue its parameters.
fn walk_sort<'a>(
    sort: &'a FrontendSort,
    depth: u32,
    shape: &mut ParsedRootShape,
    pending: &mut Vec<Node<'a>>,
) {
    match sort {
        FrontendSort::Simple(name) => {
            shape.bytes = shape.bytes.saturating_add(name.len() as u64);
        }
        FrontendSort::Parameterized(name, parameters) => {
            shape.bytes = shape
                .bytes
                .saturating_add(name.len() as u64)
                .saturating_add(parameters.len() as u64 + 2);
            pending.extend(
                parameters
                    .iter()
                    .map(|p| Node::Sort(p, depth.saturating_add(1))),
            );
        }
        FrontendSort::Indexed(name, _) => {
            shape.bytes = shape.bytes.saturating_add(name.len() as u64 + 4);
        }
        _ => shape.unpriced = shape.unpriced.saturating_add(1),
    }
}

/// Price one annotation s-expression and queue its items.
fn walk_sexpr<'a>(
    sexpr: &'a SExpr,
    depth: u32,
    shape: &mut ParsedRootShape,
    pending: &mut Vec<Node<'a>>,
) {
    match sexpr {
        SExpr::List(items) => {
            shape.bytes = shape.bytes.saturating_add(items.len() as u64 + 2);
            pending.extend(
                items
                    .iter()
                    .map(|i| Node::SExpr(i, depth.saturating_add(1))),
            );
        }
        _ => shape.bytes = shape.bytes.saturating_add(4),
    }
}
