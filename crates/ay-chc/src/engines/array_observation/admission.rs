// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conservative occurrence/depth/fanout admission before opaque scalarization.
//! Every occurrence is counted, so DAG sharing cannot hide recursive rewrite
//! expansion. These private finite caps decline to the ordinary engine; they
//! are neither policy flags nor a cumulative AST/RSS or hard-latency ledger.

use super::super::array_projection::expression::checked_sort_with_bound;
use crate::expr::dag::children;
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ClauseHead, PredicateId};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

pub(super) const MAX_NODES: usize = 8192;
pub(super) const MAX_DEPTH: usize = 32;
pub(super) const MAX_ARITY: usize = 64;
const MAX_PREDICATES: usize = 128;
const MAX_CLAUSES: usize = 512;
const MAX_ARGUMENTS: usize = 4096;
const MAX_SELECTS: usize = 16;
const MAX_TEXT: usize = 65536;

fn scalar(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Bool | ChcSort::Int | ChcSort::Real)
        || matches!(sort, ChcSort::BitVec(width) if *width > 0 && *width <= 128)
}

pub(super) fn bounded_sort(sort: &ChcSort) -> bool {
    scalar(sort)
        || matches!(sort, ChcSort::Array(key, value)
        if (matches!(key.as_ref(), ChcSort::Int) || matches!(key.as_ref(), ChcSort::BitVec(width) if *width > 0 && *width <= 128))
            && scalar(value))
}

#[derive(Default)]
pub(super) struct Scan {
    nodes: usize,
    text: usize,
    selects: usize,
}

impl Scan {
    pub(super) fn text(&mut self, text: &str) -> Option<()> {
        if text.len() > 1024 {
            return None;
        }
        self.text = self.text.checked_add(text.len())?;
        (self.text <= MAX_TEXT).then_some(())
    }

    pub(super) fn expression(
        &mut self,
        root: &ChcExpr,
        poll: &mut dyn FnMut() -> bool,
    ) -> Option<()> {
        if !poll() {
            return None;
        }
        // DFS frontier <= depth * fanout. Reserve this bounded amount BEFORE
        // walking; no unchecked input-sized child census is allocated.
        let mut pending = Vec::new();
        pending.try_reserve_exact(MAX_DEPTH * MAX_ARITY).ok()?;
        pending.push((root, 1usize));
        while let Some((node, depth)) = pending.pop() {
            self.nodes = self.nodes.checked_add(1)?;
            if !poll() || depth > MAX_DEPTH || self.nodes > MAX_NODES {
                return None;
            }
            match node {
                ChcExpr::Var(variable) => {
                    self.text(&variable.name)?;
                    if !bounded_sort(&variable.sort) {
                        return None;
                    }
                }
                ChcExpr::BitVec(_, width) if *width == 0 || *width > 128 => return None,
                ChcExpr::ConstArray(key, _) if !scalar(key) => {
                    return None;
                }
                ChcExpr::PredicateApp(..)
                | ChcExpr::FuncApp(..)
                | ChcExpr::ConstArrayMarker(..)
                | ChcExpr::IsTesterMarker(..) => return None,
                ChcExpr::Op(ChcOp::Select, _) => {
                    self.selects = self.selects.checked_add(1)?;
                    if self.selects > MAX_SELECTS {
                        return None;
                    }
                }
                _ => {}
            }
            let descendants = children(node);
            if descendants.len() > MAX_ARITY {
                return None;
            }
            for child in descendants.iter().rev() {
                if !poll() || pending.len() >= MAX_DEPTH * MAX_ARITY {
                    return None;
                }
                pending.push((child.as_ref(), depth.checked_add(1)?));
            }
        }
        poll().then_some(())
    }
}

/// Budget/type every owned root and complete frozen snapshot BEFORE clone or
/// validation, on one conservative scan and under each registry's own types.
/// The constructor freezes one source with no nested provenance; decline
/// unexpected nested history rather than recurse or silently omit a registry.
pub(super) fn problem(problem: &ChcProblem, poll: &mut dyn FnMut() -> bool) -> Option<usize> {
    let mut scan = Scan::default();
    registry(problem, &mut scan, poll)?;
    if let Some(source) = problem.frozen_pruned_source_for_budget() {
        if !poll() || source.frozen_pruned_source_for_budget().is_some() {
            return None;
        }
        registry(source, &mut scan, poll)?;
    }
    poll().then_some(scan.selects)
}

fn registry(problem: &ChcProblem, scan: &mut Scan, poll: &mut dyn FnMut() -> bool) -> Option<()> {
    if !poll()
        || problem.predicates().is_empty()
        || problem.predicates().len() > MAX_PREDICATES
        || !problem.datatype_defs().is_empty()
        || problem.action_names().len() > MAX_CLAUSES
    {
        return None;
    }
    let mut names = DetHashSet::default();
    let mut arguments = 0usize;
    for (index, predicate) in problem.predicates().iter().enumerate() {
        scan.text(&predicate.name)?;
        if !poll()
            || predicate.id.index() != index
            || !names.insert(predicate.name.as_str())
            || predicate.arg_sorts.len() > MAX_ARITY
            || problem.lookup_predicate(&predicate.name) != Some(predicate.id)
        {
            return None;
        }
        arguments = arguments.checked_add(predicate.arg_sorts.len())?;
        if arguments > MAX_ARGUMENTS || !predicate.arg_sorts.iter().all(bounded_sort) {
            return None;
        }
    }
    for name in problem.action_names() {
        if !poll() {
            return None;
        }
        scan.text(name)?;
    }
    owned_roots(problem, scan, poll)?;
    for clause in problem.source_clauses() {
        if !poll() {
            return None;
        }
        authenticate_clause(problem, clause, poll)?;
    }
    poll().then_some(())
}

fn owned_roots(
    problem: &ChcProblem,
    scan: &mut Scan,
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    let mut count = 0usize;
    // Unlike source_clauses, this includes OWNED pruned roots even when an
    // earlier transform froze another registry. Clone still copies these.
    for clause in problem.owned_clauses_for_budget() {
        count = count.checked_add(1)?;
        if !poll() || count > MAX_CLAUSES || clause.body.predicates.len() > MAX_ARITY {
            return None;
        }
        // First occurrence-price every root before typing allocates a memo.
        for (_, args) in &clause.body.predicates {
            if args.len() > MAX_ARITY {
                return None;
            }
            for argument in args {
                scan.expression(argument, poll)?;
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            scan.expression(constraint, poll)?;
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            if args.len() > MAX_ARITY {
                return None;
            }
            for argument in args {
                scan.expression(argument, poll)?;
            }
        }
    }
    poll().then_some(())
}

fn authenticate_clause(
    problem: &ChcProblem,
    clause: &crate::HornClause,
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    let mut variables = DetHashMap::<String, ChcSort>::default();
    for (id, args) in &clause.body.predicates {
        arguments(problem, *id, args, &mut variables, poll)?;
    }
    if let Some(constraint) = &clause.body.constraint {
        if typed(constraint, &mut variables, poll)? != ChcSort::Bool {
            return None;
        }
    }
    if let ClauseHead::Predicate(id, args) = &clause.head {
        arguments(problem, *id, args, &mut variables, poll)?;
    }
    poll().then_some(())
}

fn arguments(
    problem: &ChcProblem,
    id: PredicateId,
    args: &[ChcExpr],
    variables: &mut DetHashMap<String, ChcSort>,
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    let predicate = problem.get_predicate(id)?;
    if predicate.id != id || args.len() != predicate.arg_sorts.len() {
        return None;
    }
    for (arg, sort) in args.iter().zip(&predicate.arg_sorts) {
        if !poll() || &typed(arg, variables, poll)? != sort {
            return None;
        }
    }
    Some(())
}

fn typed(
    expr: &ChcExpr,
    variables: &mut DetHashMap<String, ChcSort>,
    poll: &mut dyn FnMut() -> bool,
) -> Option<ChcSort> {
    checked_sort_with_bound(
        expr,
        poll,
        &mut |var| match variables.get(&var.name) {
            Some(sort) => sort == &var.sort,
            None => {
                variables.insert(var.name.clone(), var.sort.clone());
                true
            }
        },
        &mut |sort| bounded_sort(sort),
    )
}

/// Conservative pre-transform bound: every array could observe every select.
pub(super) fn projected_arity(
    problem: &ChcProblem,
    selects: usize,
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    if selects == 0 {
        return None;
    }
    let mut total = 0usize;
    for predicate in problem.predicates() {
        if !poll() {
            return None;
        }
        let mut count = 0usize;
        for sort in &predicate.arg_sorts {
            if !poll() {
                return None;
            }
            count = count.checked_add(if matches!(sort, ChcSort::Array(..)) {
                selects
            } else {
                1
            })?;
        }
        total = total.checked_add(count)?;
        if count > MAX_ARITY || total > MAX_ARGUMENTS {
            return None;
        }
    }
    Some(())
}
