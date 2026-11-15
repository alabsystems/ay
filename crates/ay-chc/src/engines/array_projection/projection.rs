// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Argument erasure for Safe candidate search only. For a fixed map, lifting
//! `P'(kept)` to `P(all) = P'(kept)` makes every original clause identical to
//! its projected interpretation. An Unsafe result does NOT lift this way.
//! Original constraints, actions and query metadata are never rewritten.
//!
//! This initial candidate slice admits scalar sorts and flat scalar arrays;
//! unsupported sorts/functions decline, not a claim of general array support.
//! Remaining array constraints and joins are preserved, not grounds for
//! rejection. Polls and fallible Vec reservations do not constitute a cumulative
//! AST-byte/RSS allowance or a hard latency bound: registry/AST clones, map and
//! string allocation, and cleanup remain opaque to this cooperative boundary.

use ay_core::kani_compat::{DetHashMap, DetHashSet};

use super::expression::{checked_sort, supported_sort};
use crate::{ChcExpr, ChcProblem, ChcSort, ClauseHead, PredicateId};

pub(super) struct Columns {
    pub(super) id: PredicateId,
    pub(super) original: Vec<ChcSort>,
    pub(super) kept: Vec<usize>,
}

/// No proof or reversible-transform authority: callers must validate a lifted
/// candidate against the unchanged original problem before admitting Safe.
pub(super) struct Projection {
    pub(super) columns: Vec<Columns>,
    reduced: ChcProblem,
}

impl Projection {
    /// `None` means unsupported, malformed, unchanged, or interrupted. The
    /// caller owns sticky cancellation and cleanup/publication observations.
    pub(super) fn new(problem: &ChcProblem, poll: &mut dyn FnMut() -> bool) -> Option<Self> {
        let columns = columns(problem, poll)?;
        authenticate_clauses(problem, &columns, poll)?;
        if !poll() {
            return None;
        }
        // Clone preserves all private metadata, including original pruned
        // query evidence; the signature helper freezes that source registry.
        let mut reduced = problem.clone();
        let mut kept = Vec::new();
        if !poll() {
            return None;
        }
        kept.try_reserve_exact(columns.len()).ok()?;
        for column in &columns {
            if !poll() {
                return None;
            }
            kept.push(column.kept.clone());
        }
        reduced.project_predicate_signatures(&kept, poll)?;
        drop(kept);
        for clause in reduced.clauses_mut() {
            if !poll() {
                return None;
            }
            for (id, arguments) in &mut clause.body.predicates {
                project_arguments(*id, arguments, &columns, poll)?;
            }
            if let ClauseHead::Predicate(id, arguments) = &mut clause.head {
                project_arguments(*id, arguments, &columns, poll)?;
            }
        }
        poll().then_some(Self { columns, reduced })
    }

    pub(super) fn reduced(&self) -> &ChcProblem {
        &self.reduced
    }
}

fn columns(problem: &ChcProblem, poll: &mut dyn FnMut() -> bool) -> Option<Vec<Columns>> {
    if !poll() {
        return None;
    }
    let mut columns = Vec::new();
    columns.try_reserve_exact(problem.predicates().len()).ok()?;
    let mut names = DetHashSet::default();
    let mut changed = false;
    for (index, predicate) in problem.predicates().iter().enumerate() {
        if !poll()
            || predicate.id.index() != index
            || !names.insert(predicate.name.as_str())
            || problem.lookup_predicate(&predicate.name) != Some(predicate.id)
        {
            return None;
        }
        let mut kept = Vec::new();
        kept.try_reserve_exact(predicate.arg_sorts.len()).ok()?;
        for (position, sort) in predicate.arg_sorts.iter().enumerate() {
            if !poll() || !supported_sort(sort) {
                return None;
            }
            if matches!(sort, ChcSort::Array(..)) {
                changed = true;
            } else {
                kept.push(position);
            }
        }
        columns.push(Columns {
            id: predicate.id,
            original: predicate.arg_sorts.clone(),
            kept,
        });
    }
    drop(names);
    (changed && poll()).then_some(columns)
}

fn authenticate_clauses(
    problem: &ChcProblem,
    columns: &[Columns],
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    // Also authenticate unfrozen pruned-query clauses in this registry. Older
    // frozen provenance keeps its own registry and is checked at the original
    // verifier boundary; it must not be reinterpreted using this live map.
    for clause in problem.source_clauses() {
        if !poll() {
            return None;
        }
        let mut variables = DetHashMap::default();
        for (id, arguments) in &clause.body.predicates {
            authenticate_arguments(*id, arguments, columns, &mut variables, poll)?;
        }
        if let Some(constraint) = &clause.body.constraint {
            let sort = checked_sort(constraint, poll, &mut |var| {
                bind_variable(&mut variables, var)
            })?;
            if sort != ChcSort::Bool {
                return None;
            }
        }
        if let ClauseHead::Predicate(id, arguments) = &clause.head {
            authenticate_arguments(*id, arguments, columns, &mut variables, poll)?;
        }
    }
    poll().then_some(())
}

fn bind_variable(variables: &mut DetHashMap<String, ChcSort>, var: &crate::ChcVar) -> bool {
    match variables.get(&var.name) {
        Some(sort) => sort == &var.sort,
        None => {
            variables.insert(var.name.clone(), var.sort.clone());
            true
        }
    }
}

fn authenticate_arguments(
    id: PredicateId,
    arguments: &[ChcExpr],
    columns: &[Columns],
    variables: &mut DetHashMap<String, ChcSort>,
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    if !poll() {
        return None;
    }
    let column = columns.get(id.index())?;
    if column.id != id || arguments.len() != column.original.len() {
        return None;
    }
    for (argument, expected) in arguments.iter().zip(&column.original) {
        let actual = checked_sort(argument, poll, &mut |var| bind_variable(variables, var))?;
        if &actual != expected {
            return None;
        }
    }
    Some(())
}

fn project_arguments(
    id: PredicateId,
    arguments: &mut Vec<ChcExpr>,
    columns: &[Columns],
    poll: &mut dyn FnMut() -> bool,
) -> Option<()> {
    if !poll() {
        return None;
    }
    let column = columns.get(id.index())?;
    if column.id != id || arguments.len() != column.original.len() {
        return None;
    }
    let mut projected = Vec::new();
    projected.try_reserve_exact(column.kept.len()).ok()?;
    for &position in &column.kept {
        if !poll() {
            return None;
        }
        projected.push(arguments.get(position)?.clone());
    }
    *arguments = projected;
    poll().then_some(())
}
