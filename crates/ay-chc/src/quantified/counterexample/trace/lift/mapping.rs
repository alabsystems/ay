// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Occurrence coordinates only. The caller authenticates the retained source,
//! query association and exact slice pins; this mapper grants no SAT authority.

use super::*;
use crate::quantified::QuantifiedChcClauseOrigin;

pub(super) fn map(
    trace: &QuantifiedChcTrace,
    id: &QuantifiedChcQueryId,
    control: &SourceControl<'_>,
) -> Option<derivation::Derivation> {
    control.poll()?;
    let indices = trace.clause_indices();
    let premises = trace.premise_steps();
    let count = indices.len();
    let root = count.checked_sub(1)?;
    if premises.len() != count {
        return None;
    }
    // Admit the borrowed row census before walking it. A rooted occurrence
    // tree has exactly n-1 edges, independently of source recursion or arity.
    control.debit(count, 0)?;
    let mut edges_left = root;
    for edges in premises {
        control.poll()?;
        edges_left = edges_left.checked_sub(edges.len())?;
    }
    if edges_left != 0 {
        return None;
    }
    let (root_clause, appended_query) = root_origin(id, id.clause_origin(indices[root])?)?;
    let extra = usize::from(appended_query.is_some());
    let output_count = count.checked_add(extra)?;
    let output_edges = root.checked_add(extra)?;
    let bytes = output_count
        .checked_mul(std::mem::size_of::<usize>().checked_add(std::mem::size_of::<Vec<usize>>())?)?
        .checked_add(output_edges.checked_mul(std::mem::size_of::<usize>())?)?
        .checked_add(count)?;
    // Pay all retained vectors and temporary consumer storage before the first
    // allocation/copy. Work includes origin lookup, edge checks/copy and the
    // final consumer scan; per-row/edge polls share the caller's sticky control.
    let work = count
        .checked_mul(4)?
        .checked_add(root.checked_mul(3)?)?
        .checked_add(extra)?
        .checked_add(1)?;
    control.debit(work, bytes)?;
    let mut consumers = Vec::new();
    consumers.try_reserve_exact(count).ok()?;
    consumers.resize(count, 0u8);
    let mut clause_indices = Vec::new();
    clause_indices.try_reserve_exact(output_count).ok()?;
    let mut premise_steps = Vec::new();
    premise_steps.try_reserve_exact(output_count).ok()?;
    for (occurrence, (&index, edges)) in indices.iter().zip(premises).enumerate() {
        control.poll()?;
        let mapped = if occurrence == root {
            root_clause
        } else {
            match id.clause_origin(index)? {
                QuantifiedChcClauseOrigin::Source { clause_index }
                    if clause_index != id.query_clause_index() =>
                {
                    clause_index
                }
                _ => return None,
            }
        };
        for &predecessor in edges {
            control.poll()?;
            if predecessor >= occurrence || consumers[predecessor] != 0 {
                return None;
            }
            consumers[predecessor] = 1;
        }
        let mut copied = Vec::new();
        copied.try_reserve_exact(edges.len()).ok()?;
        copied.extend_from_slice(edges);
        clause_indices.push(mapped);
        premise_steps.push(copied);
    }
    for &consumer in &consumers[..root] {
        control.poll()?;
        if consumer != 1 {
            return None;
        }
    }
    if let Some(query) = appended_query {
        let mut edge = Vec::new();
        edge.try_reserve_exact(1).ok()?;
        edge.push(root);
        clause_indices.push(query);
        premise_steps.push(edge);
    }
    drop(consumers);
    control.poll()?;
    Some(derivation::Derivation {
        clause_indices,
        premise_steps,
    })
}

fn root_origin(
    id: &QuantifiedChcQueryId,
    origin: QuantifiedChcClauseOrigin,
) -> Option<(usize, Option<usize>)> {
    match origin {
        QuantifiedChcClauseOrigin::Source { clause_index }
            if id.defining_clause_index().is_none() && clause_index == id.query_clause_index() =>
        {
            Some((clause_index, None))
        }
        QuantifiedChcClauseOrigin::UnfoldedMarker {
            defining_clause_index,
            query_clause_index,
        } if id.defining_clause_index() == Some(defining_clause_index)
            && id.query_clause_index() == query_clause_index
            && defining_clause_index != query_clause_index =>
        {
            Some((defining_clause_index, Some(query_clause_index)))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests;
