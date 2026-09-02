// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed body/head ghost-index alignment for the raw array transformation.

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::{ChcExpr, ChcVar, ClauseHead, HornClause};

use super::{
    instantiation_tuples, observed_access_tuple, GhostPairSpec, GhostPredSpec, BODY_INSTANCE_CAP,
};

/// Align body probes with distinct compatible head probes. Exact array-variable
/// identity handles permutations; the legacy typed tuple remains the fallback.
pub(super) fn aligned_body_ghost_indices(
    body_spec: &GhostPredSpec,
    body_args: &[ChcExpr],
    head_spec: &GhostPredSpec,
    head_args: &[ChcExpr],
    pairs_per_array: usize,
    fresh_head_indices: &[ChcExpr],
    trigger_indices: &[ChcExpr],
) -> Option<Vec<ChcExpr>> {
    if pairs_per_array == 0
        || body_args.len() != body_spec.original_arity
        || head_args.len() != head_spec.original_arity
        || fresh_head_indices.len() != head_spec.slots(pairs_per_array)
    {
        return None;
    }
    let head_arrays = unique_instrumented_arrays(head_spec, head_args)?;
    let body_arrays = unique_instrumented_arrays(body_spec, body_args)?;
    let body_to_head = aligned_array_ordinals(
        body_spec,
        body_args,
        &body_arrays,
        head_spec,
        head_args,
        &head_arrays,
    )?;
    let fallback = instantiation_tuples(
        &body_spec.slot_index_sorts(pairs_per_array),
        fresh_head_indices,
        trigger_indices,
        BODY_INSTANCE_CAP,
    )
    .into_iter()
    .next()?;
    let mut tuple = Vec::with_capacity(body_spec.slots(pairs_per_array));

    for (body_ordinal, body_position) in body_spec.array_positions.iter().enumerate() {
        let index_sort = body_spec.index_sorts.get(body_ordinal)?;
        let body_sort = body_args.get(*body_position)?.sort();
        for pair in 0..pairs_per_array {
            let mapped = body_to_head
                .get(body_ordinal)
                .copied()
                .flatten()
                .and_then(|ordinal| {
                    let head_position = *head_spec.array_positions.get(ordinal)?;
                    (head_args.get(head_position)?.sort() == body_sort
                        && head_spec.index_sorts.get(ordinal) == Some(index_sort))
                    .then_some(ordinal)
                    .and_then(|ordinal| ordinal.checked_mul(pairs_per_array))
                    .and_then(|base| base.checked_add(pair))
                    .and_then(|slot| fresh_head_indices.get(slot).cloned())
                });
            let body_slot = body_ordinal
                .checked_mul(pairs_per_array)?
                .checked_add(pair)?;
            tuple.push(mapped.or_else(|| fallback.get(body_slot).cloned())?);
        }
    }
    Some(tuple)
}

/// Lock exact array-variable matches first, then give every remaining body
/// array a distinct compatible head probe where possible.
fn aligned_array_ordinals(
    body_spec: &GhostPredSpec,
    body_args: &[ChcExpr],
    body_arrays: &FxHashMap<ChcVar, usize>,
    head_spec: &GhostPredSpec,
    head_args: &[ChcExpr],
    head_arrays: &FxHashMap<ChcVar, usize>,
) -> Option<Vec<Option<usize>>> {
    let mut alignment = vec![None; body_spec.array_positions.len()];
    let mut used_head = vec![false; head_spec.array_positions.len()];

    for (variable, body_ordinal) in body_arrays {
        let Some(head_ordinal) = head_arrays.get(variable).copied() else {
            continue;
        };
        if !array_ordinals_compatible(
            body_spec,
            body_args,
            *body_ordinal,
            head_spec,
            head_args,
            head_ordinal,
        )? {
            continue;
        }
        alignment[*body_ordinal] = Some(head_ordinal);
        used_head[head_ordinal] = true;
    }
    for (body_ordinal, entry) in alignment.iter_mut().enumerate() {
        if entry.is_some() {
            continue;
        }
        let head_ordinal = (0..head_spec.array_positions.len()).find(|head_ordinal| {
            !used_head[*head_ordinal]
                && array_ordinals_compatible(
                    body_spec,
                    body_args,
                    body_ordinal,
                    head_spec,
                    head_args,
                    *head_ordinal,
                ) == Some(true)
        });
        if let Some(head_ordinal) = head_ordinal {
            *entry = Some(head_ordinal);
            used_head[head_ordinal] = true;
        }
    }
    Some(alignment)
}

fn array_ordinals_compatible(
    body_spec: &GhostPredSpec,
    body_args: &[ChcExpr],
    body_ordinal: usize,
    head_spec: &GhostPredSpec,
    head_args: &[ChcExpr],
    head_ordinal: usize,
) -> Option<bool> {
    let body_position = *body_spec.array_positions.get(body_ordinal)?;
    let head_position = *head_spec.array_positions.get(head_ordinal)?;
    Some(
        body_args.get(body_position)?.sort() == head_args.get(head_position)?.sort()
            && body_spec.index_sorts.get(body_ordinal) == head_spec.index_sorts.get(head_ordinal),
    )
}

/// Pick the raw-transform body tuple in semantic priority order: an observed
/// query access, head/body alignment, then the established trigger fallback.
pub(super) fn preferred_body_ghost_indices(
    clause: &HornClause,
    spec: &GhostPairSpec,
    body_spec: &GhostPredSpec,
    body_args: &[ChcExpr],
    fresh_head_indices: &[ChcExpr],
    trigger_indices: &[ChcExpr],
) -> Option<Vec<ChcExpr>> {
    let observed =
        if matches!(&clause.head, ClauseHead::False) {
            clause.body.constraint.as_ref().and_then(|constraint| {
                observed_access_tuple(body_spec, spec.n, body_args, constraint)
            })
        } else {
            None
        };
    let aligned = match &clause.head {
        ClauseHead::Predicate(head_predicate, head_args) => {
            spec.preds.get(head_predicate).and_then(|head_spec| {
                aligned_body_ghost_indices(
                    body_spec,
                    body_args,
                    head_spec,
                    head_args,
                    spec.n,
                    fresh_head_indices,
                    trigger_indices,
                )
            })
        }
        ClauseHead::False => None,
    };
    observed.or(aligned).or_else(|| {
        instantiation_tuples(
            &body_spec.slot_index_sorts(spec.n),
            fresh_head_indices,
            trigger_indices,
            BODY_INSTANCE_CAP,
        )
        .into_iter()
        .next()
    })
}

fn unique_instrumented_arrays(
    spec: &GhostPredSpec,
    args: &[ChcExpr],
) -> Option<FxHashMap<ChcVar, usize>> {
    let mut counts: FxHashMap<String, (ChcVar, usize, bool)> = FxHashMap::default();
    for (ordinal, position) in spec.array_positions.iter().enumerate() {
        let argument = args.get(*position)?;
        let ChcExpr::Var(variable) = argument else {
            continue;
        };
        if let Some((_, _, repeated)) = counts.get_mut(&variable.name) {
            *repeated = true;
        } else {
            counts.insert(variable.name.clone(), (variable.clone(), ordinal, false));
        }
    }
    Some(
        counts
            .into_values()
            .filter_map(|(variable, ordinal, repeated)| (!repeated).then_some((variable, ordinal)))
            .collect(),
    )
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "ghost_tuple_flow_tests.rs"]
mod tests;
