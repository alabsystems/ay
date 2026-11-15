// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-clause occurrence topology, without model or proof authority.
//! Every non-root occurrence is consumed exactly once. Repeated source clauses
//! are separate occurrences, not shared assignments or memoized predicates.

use super::{QuantifiedChcProblem, SourceControl};
use crate::{ChcError, ClauseHead, PredicateId};
use sha2::{Digest, Sha256};

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Derivation {
    pub(super) clause_indices: Vec<usize>,
    pub(super) premise_steps: Vec<Vec<usize>>,
}

fn refused() -> ChcError {
    ChcError::Verification("invalid original quantified derivation topology".to_owned())
}

pub(super) fn validate(
    problem: &QuantifiedChcProblem,
    indices: &[usize],
    premises: &[Vec<usize>],
    control: &SourceControl<'_>,
) -> Result<(), ChcError> {
    control.poll().ok_or_else(refused)?;
    let source = problem.source_problem();
    if indices.is_empty()
        || premises.len() != indices.len()
        || problem.premises().len() != source.clauses().len()
    {
        return Err(refused());
    }
    // Charge the complete dynamic census before allocating. Strict predecessor
    // edges plus one consumer per non-root imply root reachability; this proof
    // does not depend on a fixed depth or recursively following the edges.
    let root = indices.len() - 1;
    control.bytes(indices.len()).ok_or_else(refused)?;
    let mut consumers = Vec::new();
    consumers
        .try_reserve_exact(indices.len())
        .map_err(|_| refused())?;
    consumers.resize(indices.len(), 0u8);
    for (step, (&index, incoming)) in indices.iter().zip(premises).enumerate() {
        control.charge(1).ok_or_else(refused)?;
        let clause = source.clauses().get(index).ok_or_else(refused)?;
        if incoming.len() != clause.body.predicates.len() || incoming.len() > root {
            return Err(refused());
        }
        match &clause.head {
            ClauseHead::False if step == root => {}
            ClauseHead::Predicate(id, args) if step != root => {
                predicate(problem, *id, args.len())?;
            }
            _ => return Err(refused()),
        }
        for ((id, args), &predecessor) in clause.body.predicates.iter().zip(incoming) {
            control.charge(1).ok_or_else(refused)?;
            if predecessor >= step || consumers[predecessor] != 0 {
                return Err(refused());
            }
            predicate(problem, *id, args.len())?;
            let predecessor_clause = source
                .clauses()
                .get(indices[predecessor])
                .ok_or_else(refused)?;
            let ClauseHead::Predicate(head, head_args) = &predecessor_clause.head else {
                return Err(refused());
            };
            if id != head || args.len() != head_args.len() {
                return Err(refused());
            }
            consumers[predecessor] = 1;
        }
    }
    if consumers[..root].iter().any(|&count| count != 1) {
        return Err(refused());
    }
    drop(consumers);
    control.poll().ok_or_else(refused)
}

fn predicate(
    problem: &QuantifiedChcProblem,
    id: PredicateId,
    arity: usize,
) -> Result<(), ChcError> {
    let declaration = problem
        .source_problem()
        .predicates()
        .get(id.index())
        .ok_or_else(refused)?;
    if declaration.id != id || declaration.arg_sorts.len() != arity {
        return Err(refused());
    }
    Ok(())
}

/// Bind occurrence topology even when different nullary/identical-clause trees
/// render the same SAT conjunction. This digest is not proof authority: callers
/// still validate topology, compare full source/script and freshly validate SAT.
pub(super) fn fingerprint(
    indices: &[usize],
    premises: &[Vec<usize>],
    control: &SourceControl<'_>,
) -> Option<[u8; 32]> {
    control.poll()?;
    if indices.is_empty() || indices.len() != premises.len() {
        return None;
    }
    // A tree has exactly n-1 edges. Bound the total borrowed edge census before
    // traversing each row; no quadratic malformed adjacency table is admitted.
    let mut edges_left = indices.len().checked_sub(1)?;
    let mut hash = Sha256::new();
    hash.update(b"ay.quantified.original-occurrence-tree.v1\0");
    hash.update(u64::try_from(indices.len()).ok()?.to_le_bytes());
    for (&index, edges) in indices.iter().zip(premises) {
        control.charge(1)?;
        edges_left = edges_left.checked_sub(edges.len())?;
        hash.update(u64::try_from(index).ok()?.to_le_bytes());
        hash.update(u64::try_from(edges.len()).ok()?.to_le_bytes());
        for &edge in edges {
            control.charge(1)?;
            hash.update(u64::try_from(edge).ok()?.to_le_bytes());
        }
    }
    if edges_left != 0 {
        return None;
    }
    let result = hash.finalize().into();
    control.poll()?;
    Some(result)
}

#[cfg(test)]
mod tests;
