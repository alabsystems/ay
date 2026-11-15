// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::access::{self, AccessStep};
use super::super::layout::{Predicate, Step};
use super::*;
use crate::quantified::records::sort_bytes;
use crate::ChcOp;
use std::sync::Arc;

pub(super) fn rewrite(
    constraint: &ChcExpr,
    positions: &DetHashMap<ChcVar, usize>,
    target: PredicateId,
    transport: &[Option<usize>],
    layout: &Layout,
    control: &SourceControl<'_>,
) -> Option<ChcExpr> {
    let predicate = layout.predicate(target)?;
    let accesses = access::collect(constraint, positions, layout, control)?;
    if accesses.is_empty() {
        return None;
    }
    let mut local = DetHashMap::default();
    for access in &accesses {
        let argument = transport.get(access.argument).copied().flatten()?;
        let (_, observation) = access::matching(predicate, access, argument)?;
        for (step, actual) in observation.path.iter().zip(&access.path) {
            let (Step::Axis(axis), AccessStep::Index(ChcExpr::Var(var))) = (step, actual) else {
                continue;
            };
            if positions.contains_key(var) {
                continue;
            }
            let ghost = predicate
                .canonical
                .get(predicate.original.len().checked_add(*axis)?)?;
            if ghost.sort != var.sort {
                return None;
            }
            if !local.contains_key(var) && local.values().any(|prior| prior == ghost) {
                return None;
            }
            control.bytes(
                var.name
                    .len()
                    .checked_add(ghost.name.len())?
                    .checked_add(sort_bytes(&var.sort)?)?
                    .checked_add(sort_bytes(&ghost.sort)?)?,
            )?;
            local.entry(var.clone()).or_insert_with(|| ghost.clone());
        }
    }
    let mut context = Rewrite {
        positions,
        transport,
        layout,
        predicate,
        local,
        guards: Vec::new(),
        control,
    };
    let bad = context.expression(constraint, 0, Position::Scalar)?;
    let formula = ChcExpr::implies(
        ChcExpr::and_all_checked(context.guards, || control.poll().is_none())?,
        ChcExpr::not(bad),
    );
    source_premises::preflight(&formula, control, &mut 0)?;
    Some(formula)
}

struct Rewrite<'a, 'c> {
    positions: &'a DetHashMap<ChcVar, usize>,
    transport: &'a [Option<usize>],
    layout: &'a Layout,
    predicate: &'a Predicate,
    local: DetHashMap<ChcVar, ChcVar>,
    guards: Vec<ChcExpr>,
    control: &'a SourceControl<'c>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Position {
    Scalar,
    Index,
}

impl Rewrite<'_, '_> {
    fn expression(&mut self, expr: &ChcExpr, depth: usize, position: Position) -> Option<ChcExpr> {
        self.control.charge(1)?;
        if depth > crate::quantified::records::MAX_RECORD_DEPTH {
            return None;
        }
        if position == Position::Scalar && layout::scalar(&expr.sort()) {
            if let Some(access) =
                access::recognize(expr, self.positions, self.layout, self.control, 0)
            {
                if !access.path.is_empty() {
                    let argument = self.transport.get(access.argument).copied().flatten()?;
                    let predicate = self.predicate;
                    let (position, observation) = access::matching(predicate, &access, argument)?;
                    for (step, actual) in observation.path.iter().zip(&access.path) {
                        if let (Step::Axis(axis), AccessStep::Index(term)) = (step, actual) {
                            let term = self.expression(term, depth + 1, Position::Index)?;
                            let var = self
                                .predicate
                                .canonical
                                .get(self.predicate.original.len().checked_add(*axis)?)?;
                            if var.sort != term.sort() {
                                return None;
                            }
                            self.control
                                .bytes(var.name.len().checked_add(sort_bytes(&var.sort)?)?)?;
                            self.guards
                                .push(ChcExpr::eq(ChcExpr::var(var.clone()), term));
                        }
                    }
                    let offset = self
                        .predicate
                        .original
                        .len()
                        .checked_add(self.predicate.axes.len())?
                        .checked_add(position)?;
                    let var = self.predicate.canonical.get(offset)?;
                    if var.sort != expr.sort() {
                        return None;
                    }
                    self.control
                        .bytes(var.name.len().checked_add(sort_bytes(&var.sort)?)?)?;
                    return Some(ChcExpr::var(var.clone()));
                }
            }
        }
        Some(match expr {
            ChcExpr::Var(var) => {
                let target = if let Some(index) = self.local.get(var) {
                    index
                } else {
                    let position = *self.positions.get(var)?;
                    self.predicate
                        .canonical
                        .get(self.transport.get(position).copied().flatten()?)?
                };
                if target.sort != var.sort || !layout::scalar(&target.sort) {
                    return None;
                }
                self.control
                    .bytes(target.name.len().checked_add(sort_bytes(&target.sort)?)?)?;
                ChcExpr::var(target.clone())
            }
            ChcExpr::Op(op, args) if !matches!(op, ChcOp::Select | ChcOp::Store) => {
                self.control.charge(args.len())?;
                ChcExpr::Op(
                    *op,
                    args.iter()
                        .map(|arg| self.expression(arg, depth + 1, position).map(Arc::new))
                        .collect::<Option<Vec<_>>>()?,
                )
            }
            ChcExpr::Bool(_) => expr.clone(),
            ChcExpr::BitVec(_, width) => {
                self.control.bytes(sort_bytes(&ChcSort::BitVec(*width))?)?;
                expr.clone()
            }
            _ => return None,
        })
    }
}
