// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-node byte pricing for the bounded surface-source walk.
//!
//! A private child of `proof_trust_surgery_surface_limits` holding one arm of
//! its estimator each. Every arm is verbatim the arithmetic the single
//! `match` used to carry; splitting it is what keeps the walk and this file
//! both under their ceilings, and the `Ok(None)` fallthroughs are the same
//! "constructor the estimator does not price" answer the old `_ => None` gave.

use ay_frontend::command::{
    Constant as FrontendConstant, Index as FrontendIndex, MatchPattern as FrontendMatchPattern,
    QualifiedIdentifier as FrontendQualifiedIdentifier, Sort as FrontendSort, Term as FrontendTerm,
};
use ay_frontend::SExpr;

use super::SurfaceSourceRefusal;

/// One item of the walk's work list, with the depth it was reached at.
pub(super) enum SurfaceNode<'a> {
    Term(&'a FrontendTerm, usize),
    Sort(&'a FrontendSort, usize),
    SExpr(&'a SExpr, usize),
}

impl SurfaceNode<'_> {
    pub(super) const fn depth(&self) -> usize {
        match self {
            Self::Term(_, depth) | Self::Sort(_, depth) | Self::SExpr(_, depth) => *depth,
        }
    }
}

/// `Ok(None)` means "priced nothing": a constructor the estimator does not
/// know, which the caller turns into [`SurfaceSourceRefusal::Shape`].
type Priced = Result<Option<usize>, SurfaceSourceRefusal>;

/// How far the walk has got, and the node ceiling of the work model it prices
/// (`super::SurfaceWorkModel::max_nodes`).
#[derive(Clone, Copy)]
pub(super) struct Visit {
    pub(super) visited: usize,
    pub(super) max_nodes: usize,
}

/// Would pushing `additions` more nodes pass the node ceiling?
fn fits(visit: Visit, pending: usize, additions: usize) -> bool {
    visit
        .visited
        .saturating_add(pending)
        .saturating_add(additions)
        <= visit.max_nodes
}

fn constant_bytes(constant: &FrontendConstant) -> Option<usize> {
    Some(match constant {
        FrontendConstant::True => 4,
        FrontendConstant::False => 5,
        FrontendConstant::Numeral(value)
        | FrontendConstant::Decimal(value)
        | FrontendConstant::Hexadecimal(value)
        | FrontendConstant::Binary(value) => value.len(),
        FrontendConstant::String(value) => value.len().checked_add(2)?,
        _ => return None,
    })
}

fn indices_bytes(indices: &[FrontendIndex]) -> Option<usize> {
    indices.iter().try_fold(0usize, |bytes, index| {
        bytes.checked_add(index.text().len().saturating_add(1))
    })
}

fn qualified_identifier_bytes(identifier: &FrontendQualifiedIdentifier) -> Option<usize> {
    match identifier {
        FrontendQualifiedIdentifier::Symbol(name) => Some(name.len()),
        FrontendQualifiedIdentifier::Indexed(name, indices) => name
            .len()
            .checked_add(indices_bytes(indices)?)
            .and_then(|bytes| bytes.checked_add(4)),
        _ => None,
    }
}

/// Price one parsed term and push its children onto the walk.
pub(super) fn surface_term_bytes<'a>(
    term: &'a FrontendTerm,
    depth: usize,
    visit: Visit,
    pending: &mut Vec<SurfaceNode<'a>>,
) -> Priced {
    match term {
        FrontendTerm::Const(constant) => Ok(constant_bytes(constant)),
        FrontendTerm::Symbol(symbol) => Ok(Some(symbol.len())),
        FrontendTerm::App(..) | FrontendTerm::IndexedApp(..) | FrontendTerm::QualifiedApp(..) => {
            application_bytes(term, depth, visit, pending)
        }
        FrontendTerm::Let(..)
        | FrontendTerm::Forall(..)
        | FrontendTerm::Exists(..)
        | FrontendTerm::Lambda(..) => binder_bytes(term, depth, visit, pending),
        FrontendTerm::Match(..) | FrontendTerm::Annotated(..) => {
            match_annotation_bytes(term, depth, visit, pending)
        }
        _ => Ok(None),
    }
}

fn application_bytes<'a>(
    term: &'a FrontendTerm,
    depth: usize,
    visit: Visit,
    pending: &mut Vec<SurfaceNode<'a>>,
) -> Priced {
    match term {
        FrontendTerm::App(operator, args) | FrontendTerm::IndexedApp(operator, _, args) => {
            if !fits(visit, pending.len(), args.len()) {
                return Err(SurfaceSourceRefusal::Nodes);
            }
            for child in args {
                pending.push(SurfaceNode::Term(child, depth + 1));
            }
            let head_bytes = match term {
                FrontendTerm::IndexedApp(_, indices, _) => indices_bytes(indices)
                    .and_then(|bytes| operator.len().checked_add(bytes))
                    .and_then(|bytes| bytes.checked_add(4)),
                _ => Some(operator.len()),
            };
            Ok(head_bytes.and_then(|bytes| bytes.checked_add(args.len().saturating_add(2))))
        }
        FrontendTerm::QualifiedApp(identifier, sort, args) => {
            if !fits(visit, pending.len(), args.len().saturating_add(1)) {
                return Err(SurfaceSourceRefusal::Nodes);
            }
            for child in args {
                pending.push(SurfaceNode::Term(child, depth + 1));
            }
            pending.push(SurfaceNode::Sort(sort, depth + 1));
            Ok(qualified_identifier_bytes(identifier)
                .and_then(|bytes| bytes.checked_add(args.len().saturating_add(7))))
        }
        _ => Ok(None),
    }
}

fn binder_bytes<'a>(
    term: &'a FrontendTerm,
    depth: usize,
    visit: Visit,
    pending: &mut Vec<SurfaceNode<'a>>,
) -> Priced {
    match term {
        FrontendTerm::Let(bindings, body) => {
            if !fits(visit, pending.len(), bindings.len().saturating_add(1)) {
                return Err(SurfaceSourceRefusal::Nodes);
            }
            pending.push(SurfaceNode::Term(body, depth + 1));
            let mut bytes = 7usize;
            for (name, value) in bindings {
                pending.push(SurfaceNode::Term(value, depth + 1));
                bytes = bytes
                    .checked_add(name.len().saturating_add(3))
                    .ok_or(SurfaceSourceRefusal::Shape)?;
            }
            Ok(Some(bytes))
        }
        FrontendTerm::Forall(bindings, body)
        | FrontendTerm::Exists(bindings, body)
        | FrontendTerm::Lambda(bindings, body) => {
            if !fits(visit, pending.len(), bindings.len().saturating_add(1)) {
                return Err(SurfaceSourceRefusal::Nodes);
            }
            pending.push(SurfaceNode::Term(body, depth + 1));
            let mut bytes = 10usize;
            for (name, sort) in bindings {
                pending.push(SurfaceNode::Sort(sort, depth + 1));
                bytes = bytes
                    .checked_add(name.len().saturating_add(3))
                    .ok_or(SurfaceSourceRefusal::Shape)?;
            }
            Ok(Some(bytes))
        }
        _ => Ok(None),
    }
}

fn match_annotation_bytes<'a>(
    term: &'a FrontendTerm,
    depth: usize,
    visit: Visit,
    pending: &mut Vec<SurfaceNode<'a>>,
) -> Priced {
    match term {
        FrontendTerm::Match(scrutinee, cases) => {
            if !fits(visit, pending.len(), cases.len().saturating_add(1)) {
                return Err(SurfaceSourceRefusal::Nodes);
            }
            pending.push(SurfaceNode::Term(scrutinee, depth + 1));
            let mut bytes = 10usize;
            for (pattern, body) in cases {
                pending.push(SurfaceNode::Term(body, depth + 1));
                let pattern_bytes = match pattern {
                    FrontendMatchPattern::Symbol(name) => Some(name.len()),
                    FrontendMatchPattern::Constructor(name, variables) => variables
                        .iter()
                        .try_fold(name.len().saturating_add(2), |bytes, variable| {
                            bytes.checked_add(variable.len().saturating_add(1))
                        }),
                    _ => None,
                };
                bytes = pattern_bytes
                    .and_then(|pattern_bytes| bytes.checked_add(pattern_bytes.saturating_add(3)))
                    .ok_or(SurfaceSourceRefusal::Shape)?;
            }
            Ok(Some(bytes))
        }
        // Collectors strip annotations before rendering, but every
        // parsed-source snapshot still clones their complete payload.
        FrontendTerm::Annotated(body, annotations) => {
            if !fits(visit, pending.len(), annotations.len().saturating_add(1)) {
                return Err(SurfaceSourceRefusal::Nodes);
            }
            pending.push(SurfaceNode::Term(body, depth + 1));
            let mut bytes = 0usize;
            for (name, value) in annotations {
                pending.push(SurfaceNode::SExpr(value, depth + 1));
                bytes = bytes
                    .checked_add(name.len().saturating_add(1))
                    .ok_or(SurfaceSourceRefusal::Shape)?;
            }
            Ok(Some(bytes))
        }
        _ => Ok(None),
    }
}

/// Price one parsed sort and push its parameters onto the walk.
pub(super) fn surface_sort_bytes<'a>(
    sort: &'a FrontendSort,
    depth: usize,
    visit: Visit,
    pending: &mut Vec<SurfaceNode<'a>>,
) -> Priced {
    match sort {
        FrontendSort::Simple(name) => Ok(Some(name.len())),
        FrontendSort::Parameterized(name, parameters) => {
            if !fits(visit, pending.len(), parameters.len()) {
                return Err(SurfaceSourceRefusal::Nodes);
            }
            for parameter in parameters {
                pending.push(SurfaceNode::Sort(parameter, depth + 1));
            }
            Ok(name.len().checked_add(parameters.len().saturating_add(2)))
        }
        FrontendSort::Indexed(name, indices) => Ok(indices_bytes(indices)
            .and_then(|bytes| name.len().checked_add(bytes))
            .and_then(|bytes| bytes.checked_add(4))),
        _ => Ok(None),
    }
}

/// Price one annotation s-expression and push its items onto the walk.
pub(super) fn surface_sexpr_bytes<'a>(
    sexpr: &'a SExpr,
    depth: usize,
    visit: Visit,
    pending: &mut Vec<SurfaceNode<'a>>,
) -> Priced {
    match sexpr {
        SExpr::Symbol(value)
        | SExpr::Keyword(value)
        | SExpr::Numeral(value)
        | SExpr::Decimal(value)
        | SExpr::Hexadecimal(value)
        | SExpr::Binary(value) => Ok(Some(value.len())),
        SExpr::String(value) => Ok(value.len().checked_mul(2).and_then(|n| n.checked_add(2))),
        SExpr::True => Ok(Some(4)),
        SExpr::False => Ok(Some(5)),
        SExpr::List(items) => {
            if !fits(visit, pending.len(), items.len()) {
                return Err(SurfaceSourceRefusal::Nodes);
            }
            for item in items {
                pending.push(SurfaceNode::SExpr(item, depth + 1));
            }
            Ok(Some(items.len().saturating_add(2)))
        }
        _ => Ok(None),
    }
}
