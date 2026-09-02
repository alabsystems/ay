// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded, problem-derived modulus candidates for modular equalities.

use super::*;
use std::collections::BTreeMap;

pub(super) const MAX_MODULAR_EQUALITY_MODULUS: i128 = 256;
pub(super) const MODULAR_EQUALITY_SCAN_NODE_BUDGET: usize = 16_384;

const MAX_MODULI_PER_PREDICATE: usize = 8;
const MAX_SCAN_DEPTH: usize = 128;

const PRIORITY_EXPLICIT_MODULUS: u8 = 0;
const PRIORITY_INCREMENT_OR_GUARD: u8 = 1;
const PRIORITY_GUARD_SUCCESSOR: u8 = 2;

#[derive(Default)]
struct ModulusCandidates {
    priorities: BTreeMap<i128, u8>,
}

type Definitions = BTreeMap<String, Option<ChcExpr>>;

impl ModulusCandidates {
    fn insert_i128(&mut self, value: i128, priority: u8) {
        let Some(value) = value.checked_abs() else {
            return;
        };
        self.insert_positive(value, priority);
    }

    fn insert_u128(&mut self, value: u128, priority: u8) {
        let Ok(value) = i128::try_from(value) else {
            return;
        };
        self.insert_positive(value, priority);
    }

    fn insert_positive(&mut self, value: i128, priority: u8) {
        if !(2..=MAX_MODULAR_EQUALITY_MODULUS).contains(&value) {
            return;
        }
        self.priorities
            .entry(value)
            .and_modify(|old| *old = (*old).min(priority))
            .or_insert(priority);
    }

    fn insert_guard_literal(&mut self, expr: &ChcExpr) {
        match expr {
            ChcExpr::Int(value) => {
                self.insert_i128(*value, PRIORITY_INCREMENT_OR_GUARD);
                if let Some(successor) = value.checked_abs().and_then(|v| v.checked_add(1)) {
                    self.insert_positive(successor, PRIORITY_GUARD_SUCCESSOR);
                }
            }
            ChcExpr::BitVec(value, _) => {
                self.insert_u128(*value, PRIORITY_INCREMENT_OR_GUARD);
                if let Some(successor) = value.checked_add(1) {
                    self.insert_u128(successor, PRIORITY_GUARD_SUCCESSOR);
                }
            }
            _ => {}
        }
    }

    fn finish(self) -> Vec<i128> {
        let mut ranked: Vec<(u8, i128)> = self
            .priorities
            .into_iter()
            .map(|(modulus, priority)| (priority, modulus))
            .collect();
        ranked.sort_unstable();
        ranked.truncate(MAX_MODULI_PER_PREDICATE);

        let mut moduli: Vec<i128> = ranked.into_iter().map(|(_, modulus)| modulus).collect();
        moduli.sort_unstable();
        moduli
    }
}

impl PdrSolver {
    /// Collect candidate moduli from self-transition increments and from
    /// constants used by transition guards or explicit remainder operations.
    /// `None` means the shared structural budget was exhausted.
    pub(super) fn data_driven_modular_equality_moduli(
        &self,
        predicate: PredicateId,
        remaining_nodes: &mut usize,
    ) -> Option<Vec<i128>> {
        let canonical_vars = self.canonical_vars(predicate)?.to_vec();
        let mut candidates = ModulusCandidates::default();

        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.len() != 1 {
                continue;
            }
            let (body_predicate, body_args) = &clause.body.predicates[0];
            if *body_predicate != predicate {
                continue;
            }
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                crate::ClauseHead::False => continue,
            };
            if body_args.len() != canonical_vars.len() || head_args.len() != canonical_vars.len() {
                continue;
            }

            let mut definitions = Definitions::new();
            if let Some(constraint) = &clause.body.constraint {
                if !scan_constraint_candidates(
                    constraint,
                    &mut candidates,
                    &mut definitions,
                    remaining_nodes,
                    0,
                ) {
                    return None;
                }
            }
            for head_arg in head_args {
                if !scan_explicit_moduli(head_arg, &mut candidates, remaining_nodes, 0) {
                    return None;
                }
            }

            for ((sort, body_arg), head_arg) in canonical_vars
                .iter()
                .map(|var| &var.sort)
                .zip(body_args)
                .zip(head_args)
            {
                let resolved_head = match head_arg {
                    ChcExpr::Var(head_var) if head_arg != body_arg => {
                        match definitions.get(&head_var.name) {
                            Some(Some(definition)) => definition.clone(),
                            Some(None) | None => continue,
                        }
                    }
                    _ => head_arg.clone(),
                };
                if let Some(increment) = constant_increment(sort, body_arg, &resolved_head) {
                    candidates.insert_i128(increment, PRIORITY_INCREMENT_OR_GUARD);
                }
            }
        }

        Some(candidates.finish())
    }
}

fn take_scan_node(remaining_nodes: &mut usize, depth: usize) -> bool {
    if depth >= MAX_SCAN_DEPTH || *remaining_nodes == 0 {
        return false;
    }
    *remaining_nodes -= 1;
    true
}

fn is_guard_comparison(op: ChcOp) -> bool {
    matches!(
        op,
        ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::Lt
            | ChcOp::Le
            | ChcOp::Gt
            | ChcOp::Ge
            | ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe
    )
}

fn scan_constraint_candidates(
    expr: &ChcExpr,
    candidates: &mut ModulusCandidates,
    definitions: &mut Definitions,
    remaining_nodes: &mut usize,
    depth: usize,
) -> bool {
    if !take_scan_node(remaining_nodes, depth) {
        return false;
    }
    let ChcExpr::Op(op, args) = expr else {
        return true;
    };

    if matches!(op, ChcOp::Mod | ChcOp::BvURem) && args.len() == 2 {
        match args[1].as_ref() {
            ChcExpr::Int(value) => candidates.insert_i128(*value, PRIORITY_EXPLICIT_MODULUS),
            ChcExpr::BitVec(value, _) => candidates.insert_u128(*value, PRIORITY_EXPLICIT_MODULUS),
            _ => {}
        }
    }
    if is_guard_comparison(*op) {
        for arg in args {
            candidates.insert_guard_literal(arg);
        }
    }
    if *op == ChcOp::Eq && args.len() == 2 {
        record_definition(definitions, args[0].as_ref(), args[1].as_ref());
        record_definition(definitions, args[1].as_ref(), args[0].as_ref());
    }
    args.iter().all(|arg| {
        scan_constraint_candidates(
            arg,
            candidates,
            definitions,
            remaining_nodes,
            depth.saturating_add(1),
        )
    })
}

fn record_definition(definitions: &mut Definitions, lhs: &ChcExpr, rhs: &ChcExpr) {
    let ChcExpr::Var(variable) = lhs else {
        return;
    };
    definitions
        .entry(variable.name.clone())
        .and_modify(|old| {
            if old.as_ref() != Some(rhs) {
                *old = None;
            }
        })
        .or_insert_with(|| Some(rhs.clone()));
}

fn scan_explicit_moduli(
    expr: &ChcExpr,
    candidates: &mut ModulusCandidates,
    remaining_nodes: &mut usize,
    depth: usize,
) -> bool {
    if !take_scan_node(remaining_nodes, depth) {
        return false;
    }
    let ChcExpr::Op(op, args) = expr else {
        return true;
    };
    if matches!(op, ChcOp::Mod | ChcOp::BvURem) && args.len() == 2 {
        match args[1].as_ref() {
            ChcExpr::Int(value) => candidates.insert_i128(*value, PRIORITY_EXPLICIT_MODULUS),
            ChcExpr::BitVec(value, _) => candidates.insert_u128(*value, PRIORITY_EXPLICIT_MODULUS),
            _ => {}
        }
    }
    args.iter()
        .all(|arg| scan_explicit_moduli(arg, candidates, remaining_nodes, depth.saturating_add(1)))
}

fn constant_increment(sort: &ChcSort, body: &ChcExpr, head: &ChcExpr) -> Option<i128> {
    if head == body {
        return Some(0);
    }
    match sort {
        ChcSort::Int => int_offset(body, head),
        ChcSort::BitVec(width) => bv_offset(body, head, *width),
        _ => None,
    }
}

fn int_offset(body: &ChcExpr, head: &ChcExpr) -> Option<i128> {
    let ChcExpr::Op(op, args) = head else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    match op {
        ChcOp::Add if args[0].as_ref() == body => args[1].as_i128(),
        ChcOp::Add if args[1].as_ref() == body => args[0].as_i128(),
        ChcOp::Sub if args[0].as_ref() == body => args[1].as_i128().and_then(i128::checked_neg),
        _ => None,
    }
}

fn bv_offset(body: &ChcExpr, head: &ChcExpr, width: u32) -> Option<i128> {
    let ChcExpr::Op(op, args) = head else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let literal = |expr: &ChcExpr| match expr {
        ChcExpr::BitVec(value, literal_width) if *literal_width == width => {
            i128::try_from(*value).ok()
        }
        _ => None,
    };
    match op {
        ChcOp::BvAdd if args[0].as_ref() == body => literal(args[1].as_ref()),
        ChcOp::BvAdd if args[1].as_ref() == body => literal(args[0].as_ref()),
        ChcOp::BvSub if args[0].as_ref() == body => {
            literal(args[1].as_ref()).and_then(i128::checked_neg)
        }
        _ => None,
    }
}
