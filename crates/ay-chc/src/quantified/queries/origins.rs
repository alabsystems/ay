// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source ordinals are retained during copying, never recovered from text or
//! equality searches. Structural checks below only authenticate a known pair.

use super::*;
use crate::ClauseHead;

/// Exact aggregate source origin of one clause in a quantified query slice.
/// Duplicate clauses retain distinct positional identities.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantifiedChcClauseOrigin {
    /// This slice clause is the indexed original aggregate clause.
    Source { clause_index: usize },
    /// The defining clause's complete body/premises now have a false head,
    /// composed with the original empty-premise, unconstrained nullary query.
    /// Both source identities are necessary; neither alone is this slice row.
    UnfoldedMarker {
        defining_clause_index: usize,
        query_clause_index: usize,
    },
}

pub(super) fn query_origin(plan: &plan::Plan) -> QuantifiedChcClauseOrigin {
    match plan.definition {
        Some(defining_clause_index) => QuantifiedChcClauseOrigin::UnfoldedMarker {
            defining_clause_index,
            query_clause_index: plan.query,
        },
        None => QuantifiedChcClauseOrigin::Source {
            clause_index: plan.query,
        },
    }
}

pub(super) fn reserve(
    count: usize,
    control: &Control<'_>,
) -> ChcResult<Vec<QuantifiedChcClauseOrigin>> {
    // Vec storage plus the separate Arc slice allocation/conversion; retained
    // IDs subsequently clone the immutable Arc, not the full coordinate map.
    let bytes = count
        .checked_mul(std::mem::size_of::<QuantifiedChcClauseOrigin>())
        .and_then(|bytes| bytes.checked_mul(2))
        .and_then(|bytes| bytes.checked_add(64))
        .ok_or_else(|| invalid("origin allocation overflow"))?;
    control.charge(count, bytes)?;
    let mut origins = Vec::new();
    origins
        .try_reserve_exact(count)
        .map_err(|_| invalid("origin allocation"))?;
    Ok(origins)
}

pub(super) fn seal(
    source: &QuantifiedChcProblem,
    plan: &plan::Plan,
    selected: &[bool],
    slice: &QuantifiedChcProblem,
    origins: Vec<QuantifiedChcClauseOrigin>,
    control: &Control<'_>,
) -> ChcResult<Arc<[QuantifiedChcClauseOrigin]>> {
    validate(source, plan, selected, slice, &origins, control)?;
    let origins = Arc::from(origins);
    control.poll()?;
    Ok(origins)
}

pub(super) fn validate(
    source: &QuantifiedChcProblem,
    plan: &plan::Plan,
    selected: &[bool],
    slice: &QuantifiedChcProblem,
    origins: &[QuantifiedChcClauseOrigin],
    control: &Control<'_>,
) -> ChcResult<()> {
    let source_clauses = source.source_problem().clauses();
    if selected.len() != source_clauses.len()
        || plan.query >= selected.len()
        || origins.len() != slice.source_problem().clauses().len()
        || origins.len() != slice.premises().len()
    {
        return control.refuse("origin/source alignment");
    }
    validate_query(source, plan, control)?;
    let mut slot = 0usize;
    for (index, selected) in selected.iter().enumerate() {
        control.charge(1, 0)?;
        if *selected {
            let expected = QuantifiedChcClauseOrigin::Source {
                clause_index: index,
            };
            if origins.get(slot) != Some(&expected) || source_clauses[index].is_query() {
                return control.refuse("retained origin order");
            }
            conserve(
                source,
                slice,
                index,
                slot,
                &source_clauses[index].head,
                control,
            )?;
            slot += 1;
        }
        if index == plan.query {
            if origins.get(slot) != Some(&query_origin(plan)) {
                return control.refuse("query origin order");
            }
            conserve(
                source,
                slice,
                plan.selected(),
                slot,
                &ClauseHead::False,
                control,
            )?;
            slot += 1;
        }
    }
    if slot != origins.len() {
        return control.refuse("extra clause origin");
    }
    control.poll()
}

fn validate_query(
    source: &QuantifiedChcProblem,
    plan: &plan::Plan,
    control: &Control<'_>,
) -> ChcResult<()> {
    let problem = source.source_problem();
    let query = problem
        .clauses()
        .get(plan.query)
        .ok_or_else(|| invalid("query origin"))?;
    if !query.is_query() || query.source_query_ordinal != Some(plan.ordinal) {
        return control.refuse("query ordinal origin");
    }
    if let Some(definition) = plan.definition {
        let definition = problem
            .clauses()
            .get(definition)
            .ok_or_else(|| invalid("definition origin"))?;
        let [(marker, arguments)] = query.body.predicates.as_slice() else {
            return control.refuse("marker origin arity");
        };
        if !arguments.is_empty()
            || query.body.constraint.is_some()
            || !source.premises().get(plan.query).is_some_and(Vec::is_empty)
            || !problem
                .get_predicate(*marker)
                .is_some_and(|p| p.arg_sorts.is_empty())
            || !matches!(&definition.head, ClauseHead::Predicate(id, args) if id == marker && args.is_empty())
        {
            return control.refuse("marker definition/query origin");
        }
    }
    control.poll()
}

fn conserve(
    source: &QuantifiedChcProblem,
    slice: &QuantifiedChcProblem,
    original_index: usize,
    slice_index: usize,
    head: &ClauseHead,
    control: &Control<'_>,
) -> ChcResult<()> {
    control.poll()?;
    let original = source
        .source_problem()
        .clauses()
        .get(original_index)
        .ok_or_else(|| invalid("original clause"))?;
    let actual = slice
        .source_problem()
        .clauses()
        .get(slice_index)
        .ok_or_else(|| invalid("slice clause"))?;
    let heads_match = match (head, &actual.head) {
        (ClauseHead::False, ClauseHead::False) => true,
        (ClauseHead::Predicate(p, args), ClauseHead::Predicate(q, actual)) => {
            p == q && args == actual
        }
        _ => false,
    };
    if !heads_match
        || original.body.predicates != actual.body.predicates
        || original.body.constraint != actual.body.constraint
        || original.action_id != actual.action_id
        || actual.source_query_ordinal != actual.is_query().then_some(0)
    {
        return control.refuse("copied source clause changed");
    }
    let original = source
        .premises()
        .get(original_index)
        .ok_or_else(|| invalid("original premises"))?;
    let actual = slice
        .premises()
        .get(slice_index)
        .ok_or_else(|| invalid("slice premises"))?;
    if original.len() != actual.len() {
        return control.refuse("copied premise count");
    }
    for (original, actual) in original.iter().zip(actual) {
        control.charge(1, 0)?;
        if original.binder_count() != actual.binder_count()
            || !original.binders().eq(actual.binders())
            || original.matrix() != actual.matrix()
        {
            return control.refuse("copied premise changed");
        }
    }
    control.poll()
}

#[cfg(test)]
mod tests;
