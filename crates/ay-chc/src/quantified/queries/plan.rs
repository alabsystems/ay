// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ClauseHead, HornClause, PredicateId};

pub(super) struct Plan {
    pub(super) ordinal: usize,
    pub(super) query: usize,
    pub(super) definition: Option<usize>,
    pub(super) label: String,
}

impl Plan {
    pub(super) fn selected(&self) -> usize {
        self.definition.unwrap_or(self.query)
    }
}

pub(super) fn plans(source: &QuantifiedChcProblem, control: &Control<'_>) -> ChcResult<Vec<Plan>> {
    let problem = source.source_problem();
    let mut out = Vec::new();
    let mut ordinal = 0usize;
    for (index, query) in problem.clauses().iter().enumerate() {
        control.poll()?;
        if !query.is_query() {
            continue;
        }
        if query.source_query_ordinal != Some(ordinal) {
            return control.refuse("source query ordinal mismatch");
        }
        let marker = marker(problem, query).filter(|_| source.premises()[index].is_empty());
        let mut split = false;
        if let Some(marker) = marker {
            for (definition, clause) in problem.clauses().iter().enumerate() {
                control.charge(1, 0)?;
                if matches!(&clause.head, ClauseHead::Predicate(id, args) if *id == marker && args.is_empty())
                {
                    push(&mut out, source, ordinal, index, Some(definition), control)?;
                    split = true;
                }
            }
        }
        // An undefined marker is still a syntactic (vacuously Safe) row.
        if !split {
            push(&mut out, source, ordinal, index, None, control)?;
        }
        ordinal += 1; // Immutable source admission bounds clauses at 2,048.
    }
    if out.is_empty() {
        return Err(ChcError::NoQuery);
    }
    control.poll()?;
    Ok(out)
}

fn marker(problem: &crate::ChcProblem, query: &HornClause) -> Option<PredicateId> {
    if query.body.constraint.is_some() {
        return None;
    }
    let [(id, args)] = query.body.predicates.as_slice() else {
        return None;
    };
    (args.is_empty() && problem.get_predicate(*id)?.arg_sorts.is_empty()).then_some(*id)
}

fn push(
    out: &mut Vec<Plan>,
    source: &QuantifiedChcProblem,
    ordinal: usize,
    query: usize,
    definition: Option<usize>,
    control: &Control<'_>,
) -> ChcResult<()> {
    if out.len() >= control::MAX_OBLIGATIONS {
        return control.refuse("obligation count limit");
    }
    let problem = source.source_problem();
    let selected = &problem.clauses()[definition.unwrap_or(query)];
    let direct = match selected.body.predicates.as_slice() {
        [(id, args)] if args.is_empty() => problem.get_predicate(*id).map(|p| p.name.as_str()),
        _ => None,
    };
    let fallback = match &problem.clauses()[query].body.predicates[..] {
        [(id, _)] => problem.get_predicate(*id).map(|p| p.name.as_str()),
        _ => None,
    };
    let label = if let Some(name) = direct {
        control.charge(1, name.len().saturating_add(256))?;
        name.to_owned()
    } else if let (Some(name), Some(definition)) = (fallback, definition) {
        control.charge(1, name.len().saturating_add(256))?;
        format!("{name}_definition_{definition}")
    } else {
        control.charge(1, 256)?;
        format!("query_{query}")
    };
    out.try_reserve(1).map_err(|_| invalid("plan allocation"))?;
    out.push(Plan {
        ordinal,
        query,
        definition,
        label,
    });
    Ok(())
}

pub(super) fn cone(
    source: &QuantifiedChcProblem,
    plan: &Plan,
    definitions: &[Vec<usize>],
    control: &Control<'_>,
) -> ChcResult<Vec<bool>> {
    let clauses = source.source_problem().clauses();
    control.charge(
        definitions.len().saturating_add(clauses.len()),
        definitions
            .len()
            .saturating_mul(16)
            .saturating_add(clauses.len()),
    )?;
    let mut seen = vec![false; definitions.len()];
    let mut selected = vec![false; clauses.len()];
    let mut pending = Vec::new();
    for (predicate, _) in &clauses[plan.selected()].body.predicates {
        enqueue(*predicate, &mut seen, &mut pending, control)?;
    }
    while let Some(predicate) = pending.pop() {
        control.poll()?;
        for index in &definitions[predicate] {
            control.charge(1, 0)?;
            selected[*index] = true;
            for (body, _) in &clauses[*index].body.predicates {
                enqueue(*body, &mut seen, &mut pending, control)?;
            }
        }
    }
    control.poll()?;
    Ok(selected)
}

fn enqueue(
    predicate: PredicateId,
    seen: &mut [bool],
    pending: &mut Vec<usize>,
    control: &Control<'_>,
) -> ChcResult<()> {
    control.charge(1, 0)?;
    let Some(seen) = seen.get_mut(predicate.index()) else {
        return control.refuse("unknown dependency predicate");
    };
    if !*seen {
        control.charge(1, std::mem::size_of::<usize>())?;
        pending
            .try_reserve(1)
            .map_err(|_| invalid("cone allocation"))?;
        *seen = true;
        pending.push(predicate.index());
    }
    Ok(())
}
