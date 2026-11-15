// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{
    marker, slicing, ChcQueryPlayback, ChcQueryPlaybackControl as Control,
    ChcQueryPlaybackError as Error, Origin, Result,
};
use crate::ground_derivation::{
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_CLAUSES as CLAUSES,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS as STEPS,
};
use crate::{ClauseHead, HornClause};

// The existing ordinary expansion pass uses this same semantic route ceiling.
// Playback neither raises it nor creates a new solver configuration knob.
const MAX_EXPANDED_QUERIES: usize = 512;

pub(super) fn expand<'s>(
    row: ChcQueryPlayback<'s>,
    control: &mut Control<'_>,
) -> Result<(ChcQueryPlayback<'s>, bool)> {
    control.poll()?;
    let mut queries = Vec::new();
    for (index, clause) in row.problem.clauses.iter().enumerate() {
        control.poll()?;
        if let Some(predicate) = marker(clause) {
            if clause.body.constraint.is_some() {
                return Err(Error::UnsupportedProjection);
            }
            control.push(&mut queries, (index, predicate), CLAUSES)?;
        }
    }
    let mut additions = Vec::new();
    let mut addition_origins = Vec::new();
    for &(query_index, marker) in &queries {
        for (index, clause) in row.problem.clauses.iter().enumerate() {
            control.poll()?;
            if clause.head.predicate_id() != Some(marker) {
                continue;
            }
            if additions.len() == MAX_EXPANDED_QUERIES {
                // Identical threshold disposition to the ordinary pass.
                drop(additions);
                drop(addition_origins);
                drop(queries);
                control.poll()?;
                return Ok((row, false));
            }
            let query = HornClause::query(clause.body.clone())
                .with_inherited_provenance(clause)
                .with_inherited_provenance(&row.problem.clauses[query_index]);
            let origin = compose(&row, index, query_index, control)?;
            control.push(&mut additions, query, MAX_EXPANDED_QUERIES)?;
            control.push(&mut addition_origins, origin, MAX_EXPANDED_QUERIES)?;
        }
    }
    if additions.is_empty() {
        return Ok((row, false));
    }
    let mut problem = slicing::registry(&row.problem, control)?;
    problem.next_source_query_ordinal = row.problem.next_source_query_ordinal;
    let mut origins = Vec::new();
    for (index, clause) in row.problem.clauses.iter().enumerate() {
        control.poll()?;
        let mut remove = false;
        for &(_, predicate) in &queries {
            control.poll()?;
            if marker(clause) == Some(predicate) || clause.head.predicate_id() == Some(predicate) {
                remove = true;
                break;
            }
        }
        if !remove {
            control.push(&mut problem.clauses, clause.clone(), CLAUSES)?;
            let origin = copy(&row.origins[index], control)?;
            control.push(&mut origins, origin, CLAUSES)?;
        }
    }
    for (clause, origin) in additions.into_iter().zip(addition_origins) {
        control.push(&mut problem.clauses, clause, CLAUSES)?;
        control.push(&mut origins, origin, CLAUSES)?;
    }
    slicing::admit(&problem, control)?;
    let ChcQueryPlayback {
        original,
        owner,
        id,
        problem: old_problem,
        origins: old_origins,
    } = row;
    drop(old_problem);
    drop(old_origins);
    drop(queries);
    control.poll()?;
    Ok((
        ChcQueryPlayback {
            original,
            owner,
            id,
            problem,
            origins,
        },
        true,
    ))
}

fn copy(origin: &Origin, control: &mut Control<'_>) -> Result<Origin> {
    let mut consumers = Vec::new();
    control.reserve(&mut consumers, origin.consumers.len(), STEPS)?;
    for &clause in &origin.consumers {
        control.poll()?;
        consumers.push(clause);
    }
    Ok(Origin {
        first: origin.first,
        consumers,
    })
}

fn compose(
    row: &ChcQueryPlayback<'_>,
    definition: usize,
    query: usize,
    control: &mut Control<'_>,
) -> Result<Origin> {
    let mut origin = copy(&row.origins[definition], control)?;
    let query_origin = &row.origins[query];
    for &index in std::iter::once(&query_origin.first).chain(query_origin.consumers.iter()) {
        control.poll()?;
        let clause = row
            .original
            .clauses
            .get(index)
            .ok_or(Error::InvalidSource)?;
        // These consumers have no source variables to erase: one argument-free
        // premise, no guard, and either false or an argument-free marker head.
        let nullary_body =
            matches!(clause.body.predicates.as_slice(), [(_, args)] if args.is_empty());
        let nullary_head = matches!(&clause.head, ClauseHead::False)
            || matches!(&clause.head, ClauseHead::Predicate(_, args) if args.is_empty());
        if !nullary_body || !nullary_head || clause.body.constraint.is_some() {
            return Err(Error::UnsupportedProjection);
        }
        control.push(&mut origin.consumers, index, STEPS)?;
    }
    Ok(origin)
}
