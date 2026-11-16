// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{candidate, reserve, CompactDerivation, Error, Owner, Result, MAX_DEPTH};
use crate::{ChcProblem, ClauseHead};

pub(super) fn search(
    problem: &ChcProblem,
    owner: &mut Owner<'_>,
) -> Result<Option<CompactDerivation>> {
    let mut reverse = Vec::new();
    for (index, clause) in problem.clauses().iter().enumerate() {
        owner.admit(1, 0)?;
        if matches!(clause.head, ClauseHead::False) {
            if let Some(found) = visit(problem, index, &mut reverse, owner)? {
                return Ok(Some(found));
            }
        }
    }
    Ok(None)
}

fn visit(
    problem: &ChcProblem,
    index: usize,
    reverse: &mut Vec<usize>,
    owner: &mut Owner<'_>,
) -> Result<Option<CompactDerivation>> {
    owner.admit(1, 0)?;
    if reverse.len() >= MAX_DEPTH {
        return owner.refuse(Error::Resource);
    }
    let clause = problem.clauses().get(index).ok_or(Error::InvalidSource)?;
    if clause.body.predicates.len() > 1 {
        return Ok(None); // Nonlinear Horn search is outside this producer.
    }
    reserve(reverse, 1, owner)?;
    reverse.push(index);
    let result = if let Some((required, _)) = clause.body.predicates.first() {
        owner.admit(reverse.len(), 0)?;
        let cyclic = reverse
            .iter()
            .any(|&prior| problem.clauses()[prior].head.predicate_id() == Some(*required));
        if cyclic {
            Ok(None)
        } else {
            predecessors(problem, *required, reverse, owner)
        }
    } else {
        let mut path = Vec::new();
        reserve(&mut path, reverse.len(), owner)?;
        path.extend(reverse.iter().rev().copied());
        match candidate(problem, &path, owner) {
            Err(Error::Unsupported) => Ok(None),
            other => other,
        }
    };
    reverse.pop();
    owner.poll()?;
    result
}

fn predecessors(
    problem: &ChcProblem,
    required: crate::PredicateId,
    reverse: &mut Vec<usize>,
    owner: &mut Owner<'_>,
) -> Result<Option<CompactDerivation>> {
    for (index, clause) in problem.clauses().iter().enumerate() {
        owner.admit(1, 0)?;
        if clause.head.predicate_id() == Some(required) {
            if let Some(found) = visit(problem, index, reverse, owner)? {
                return Ok(Some(found));
            }
        }
    }
    Ok(None)
}
