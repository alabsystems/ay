// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{
    marker, ChcProblem, ChcQueryObligationId, ChcQueryPlayback, ChcQueryPlaybackControl as Control,
    ChcQueryPlaybackError as Error, Origin, Result,
};
use crate::ground_derivation::{
    preflight_playback_source_with_progress, CHC_GROUND_DERIVATION_ARTIFACT_MAX_CLAUSES as CLAUSES,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREDICATES as PREDICATES,
};
use crate::{ClauseBody, HornClause, PredicateId};

pub(super) fn admit(source: &ChcProblem, control: &mut Control<'_>) -> Result<()> {
    control.poll()?;
    let result = preflight_playback_source_with_progress(source, &mut || control.poll().is_ok());
    control.poll()?;
    result?;
    Ok(())
}

pub(super) fn prepare<'s>(
    source: &'s ChcProblem,
    control: &mut Control<'_>,
) -> Result<Vec<ChcQueryPlayback<'s>>> {
    control.poll()?;
    if source.stripped_body_forall {
        return Err(Error::UnsupportedProjection);
    }
    admit(source, control)?;
    let mut rows = Vec::new();
    let mut fallback = 0usize;
    for (query_index, query) in source.clauses.iter().enumerate() {
        control.poll()?;
        if !query.is_query() {
            continue;
        }
        let ordinal = query.source_query_ordinal.unwrap_or(fallback);
        fallback = fallback.checked_add(1).ok_or(Error::LimitExceeded)?;
        let query_marker = marker(query);
        let mut definitions = Vec::new();
        if query.body.constraint.is_none() {
            if let Some(marker) = query_marker {
                for (index, clause) in source.clauses.iter().enumerate() {
                    control.poll()?;
                    if clause.head.predicate_id() == Some(marker) {
                        control.push(&mut definitions, index, CLAUSES)?;
                    }
                }
            }
        }
        if definitions.is_empty() {
            let label = match query_marker.and_then(|p| source.get_predicate(p)) {
                Some(predicate) => predicate.name.clone(),
                None => format!("query_{query_index}"),
            };
            control.poll()?;
            let row = build(
                source,
                ordinal,
                query_index,
                None,
                label,
                query.clone(),
                control,
            )?;
            control.push(&mut rows, row, CLAUSES)?;
        } else {
            for definition_index in definitions {
                control.poll()?;
                let definition = &source.clauses[definition_index];
                let mut query = HornClause::query(ClauseBody {
                    predicates: definition.body.predicates.clone(),
                    constraint: definition.body.constraint.clone(),
                });
                query.source_query_ordinal = Some(ordinal);
                let label = ChcProblem::query_obligation_label(
                    source,
                    &query,
                    query_marker.ok_or(Error::InvalidSource)?,
                    definition_index,
                );
                let row = build(
                    source,
                    ordinal,
                    query_index,
                    Some(definition_index),
                    label,
                    query,
                    control,
                )?;
                control.push(&mut rows, row, CLAUSES)?;
            }
        }
    }
    control.poll()?;
    // Absence is not a vacuity proof: this playback-only API does not validate
    // historical pruned-query owners or manufacture an empty accepted batch.
    if fallback == 0 {
        return Err(Error::UnsupportedProjection);
    }
    Ok(rows)
}

/// Copy only the registry that ordinary query slicing retains. Do not clone
/// sparse map backing capacity or the source's historical pruned query owners.
/// Individual name/sort/constructor clones are finite-source-admitted opaque
/// intervals, bracketed by polls; all wide registry loops poll explicitly.
pub(super) fn registry(source: &ChcProblem, control: &mut Control<'_>) -> Result<ChcProblem> {
    let mut result = ChcProblem::new();
    result.fixedpoint_format = source.fixedpoint_format;
    result.stripped_body_forall = source.stripped_body_forall;
    control.reserve(&mut result.predicates, source.predicates.len(), PREDICATES)?;
    result
        .predicate_names
        .try_reserve(source.predicates.len())
        .map_err(|_| Error::AllocationFailed)?;
    for predicate in &source.predicates {
        control.poll()?;
        result.predicates.push(predicate.clone());
        result
            .predicate_names
            .insert(predicate.name.clone(), predicate.id);
    }
    result
        .datatype_defs
        .try_reserve(source.datatype_defs.len())
        .map_err(|_| Error::AllocationFailed)?;
    for (name, constructors) in &source.datatype_defs {
        control.poll()?;
        let mut copied = Vec::new();
        control.reserve(&mut copied, constructors.len(), CLAUSES)?;
        for (name, selectors) in constructors {
            control.poll()?;
            let mut fields = Vec::new();
            control.reserve(&mut fields, selectors.len(), CLAUSES)?;
            for field in selectors {
                control.poll()?;
                fields.push(field.clone());
            }
            copied.push((name.clone(), fields));
        }
        result.datatype_defs.insert(name.clone(), copied);
    }
    control.reserve(&mut result.action_names, source.action_names.len(), CLAUSES)?;
    for name in &source.action_names {
        control.poll()?;
        result.action_names.push(name.clone());
    }
    control.poll()?;
    Ok(result)
}

fn build<'s>(
    source: &'s ChcProblem,
    ordinal: usize,
    query_index: usize,
    definition: Option<usize>,
    label: String,
    mut query: HornClause,
    control: &mut Control<'_>,
) -> Result<ChcQueryPlayback<'s>> {
    let selected = cone(source, &query, control)?;
    let mut problem = registry(source, control)?;
    let mut origins = Vec::new();
    // Positional selection is performed on the original ordered clause list.
    // Equal clauses intentionally retain different indices.
    for (index, clause) in source.clauses.iter().enumerate() {
        control.poll()?;
        if clause.is_query() {
            continue;
        }
        if clause
            .head
            .predicate_id()
            .is_some_and(|p| selected[p.index()])
        {
            control.push(&mut problem.clauses, clause.clone(), CLAUSES)?;
            control.push(
                &mut origins,
                Origin {
                    first: index,
                    consumers: Vec::new(),
                },
                CLAUSES,
            )?;
        }
    }
    query.source_query_ordinal = Some(0);
    problem.next_source_query_ordinal = 1;
    control.push(&mut problem.clauses, query, CLAUSES)?;
    let origin = match definition {
        Some(first) => {
            let mut consumers = Vec::new();
            control.push(&mut consumers, query_index, CLAUSES)?;
            Origin { first, consumers }
        }
        None => Origin {
            first: query_index,
            consumers: Vec::new(),
        },
    };
    control.push(&mut origins, origin, CLAUSES)?;
    admit(&problem, control)?;
    // Keep the schema from the exact canonicalization that supplies the hash.
    // The datatype-free prepared-input schema cannot label arbitrary sources.
    let identity =
        crate::proof_metadata::normalized_chc_input_identity_with_progress(&problem, &mut || {
            control.poll().is_ok()
        });
    control.poll()?;
    let (normalized_input_schema, content_sha256) = identity.map_err(|_| Error::InvalidSource)?;
    Ok(ChcQueryPlayback {
        original: source,
        owner: control.owner.clone(),
        id: ChcQueryObligationId {
            source_query_ordinal: ordinal,
            query_clause_index: query_index,
            defining_clause_index: definition,
            label,
            normalized_input_schema,
            content_sha256,
        },
        problem,
        origins,
    })
}

/// Same backwards dependency fixed point as ordinary slicing, without an
/// unpolled aggregate adjacency/clone operation. A predicate is queued once.
fn cone(source: &ChcProblem, query: &HornClause, control: &mut Control<'_>) -> Result<Vec<bool>> {
    let mut selected = Vec::new();
    control.reserve(&mut selected, source.predicates.len(), PREDICATES)?;
    for _ in &source.predicates {
        control.poll()?;
        selected.push(false);
    }
    let mut pending = Vec::new();
    for (id, _) in &query.body.predicates {
        add(*id, &mut selected, &mut pending, control)?;
    }
    while let Some(id) = pending.pop() {
        control.poll()?;
        for clause in &source.clauses {
            control.poll()?;
            if clause.head.predicate_id() == Some(id) {
                for (dependency, _) in &clause.body.predicates {
                    add(*dependency, &mut selected, &mut pending, control)?;
                }
            }
        }
    }
    Ok(selected)
}

fn add(
    id: PredicateId,
    selected: &mut [bool],
    pending: &mut Vec<PredicateId>,
    control: &mut Control<'_>,
) -> Result<()> {
    control.poll()?;
    let slot = selected.get_mut(id.index()).ok_or(Error::InvalidSource)?;
    if !*slot {
        *slot = true;
        control.push(pending, id, PREDICATES)?;
    }
    Ok(())
}
