// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Syntactic AND/OR minimum representable occurrence counts. Constraints and
//! universal premises are never simplified or evaluated here. An unavailable
//! count (unproductive or arithmetic overflow) grants no Safe authority.

use super::*;
use crate::{ClauseHead, HornClause};

pub(super) struct Index<'a> {
    pub(super) clauses: &'a [HornClause],
    pub(super) definitions: Vec<Vec<usize>>,
    pub(super) minimum: Vec<Option<usize>>,
    pub(super) costs: Vec<Option<usize>>,
}

impl<'a> Index<'a> {
    pub(super) fn new(
        problem: &'a QuantifiedChcProblem,
        control: &SourceControl<'_>,
    ) -> Option<Self> {
        let source = problem.source_problem();
        let count = source.predicates().len();
        control.charge(count)?;
        control.bytes(count.checked_mul(
            std::mem::size_of::<Vec<usize>>() + std::mem::size_of::<Option<usize>>(),
        )?)?;
        let mut definitions = Vec::new();
        definitions.try_reserve_exact(count).ok()?;
        let mut minimum = Vec::new();
        minimum.try_reserve_exact(count).ok()?;
        for (index, predicate) in source.predicates().iter().enumerate() {
            control.charge(1)?;
            if predicate.id.index() != index {
                return None;
            }
            definitions.push(Vec::new());
            minimum.push(None);
        }
        for (index, clause) in source.clauses().iter().enumerate() {
            control.charge(1)?;
            for (predicate, _) in &clause.body.predicates {
                control.charge(1)?;
                source.predicates().get(predicate.index())?;
            }
            if let ClauseHead::Predicate(predicate, _) = clause.head {
                let choices: &mut Vec<usize> = definitions.get_mut(predicate.index())?;
                control.bytes(std::mem::size_of::<usize>().checked_mul(2)?)?;
                choices.try_reserve(1).ok()?;
                choices.push(index);
            }
        }
        // Positive unit costs mean a minimum structural derivation has no
        // repeated predicate on a root-to-leaf path: replacing the ancestor by
        // the descendant would shrink it. At most #predicates relaxation rounds
        // therefore suffice, including nonlinear bodies and duplicate slots.
        for _ in 0..count {
            let mut changed = false;
            for clause in source.clauses() {
                control.charge(1)?;
                let ClauseHead::Predicate(head, _) = clause.head else {
                    continue;
                };
                let Some(cost) = clause_cost(clause, &minimum, control)? else {
                    continue;
                };
                let old = minimum.get_mut(head.index())?;
                if old.is_none_or(|old| cost < old) {
                    *old = Some(cost);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        control.bytes(
            source
                .clauses()
                .len()
                .checked_mul(std::mem::size_of::<Option<usize>>())?,
        )?;
        let mut costs = Vec::new();
        costs.try_reserve_exact(source.clauses().len()).ok()?;
        for clause in source.clauses() {
            costs.push(clause_cost(clause, &minimum, control)?);
        }
        control.poll()?;
        Some(Self {
            clauses: source.clauses(),
            definitions,
            minimum,
            costs,
        })
    }
}

fn clause_cost(
    clause: &HornClause,
    minimum: &[Option<usize>],
    control: &SourceControl<'_>,
) -> Option<Option<usize>> {
    control.charge(1)?;
    let mut cost = 1usize;
    for (predicate, _) in &clause.body.predicates {
        control.charge(1)?;
        let Some(child) = *minimum.get(predicate.index())? else {
            return Some(None);
        };
        let Some(sum) = cost.checked_add(child) else {
            // This clause cannot fit a representable occurrence vector. Do not
            // abort independent queries or hide another, cheaper definition.
            return Some(None);
        };
        cost = sum;
    }
    Some(Some(cost))
}
