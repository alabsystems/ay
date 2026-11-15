// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original composite arguments plus exact scalar observations. Finite source
//! premise instances strengthen search rules, never the sealed source.

use super::*;
use crate::quantified::records::{registry_bytes, sort_bytes};
use crate::{ChcExpr, ChcProblem, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::DetHashSet;

#[cfg(test)]
mod tests;
mod transport;

pub(super) fn problem(
    problem: &QuantifiedChcProblem,
    layout: &Layout,
    control: &SourceControl<'_>,
) -> Option<ChcProblem> {
    if !layout.matches_source(problem, control) {
        return None;
    }
    let source = problem.source_problem();
    let mut used = super::names::reserved(problem, &layout.registry, control)?;
    let mut out = ChcProblem::new();
    control.bytes(registry_bytes(source)?)?;
    for (name, constructors) in source.datatype_defs() {
        out.add_datatype_def(name.clone(), constructors.clone());
    }
    for predicate in source.predicates() {
        control.bytes(predicate.name.len())?;
        let id = out.declare_predicate(
            &predicate.name,
            layout.extended_sorts(predicate.id, control)?,
        );
        if id != predicate.id {
            return None;
        }
        for var in layout.canonical(id)? {
            control.bytes(var.name.len())?;
            used.insert(var.name.clone());
        }
    }
    for action in source.action_names() {
        control.bytes(action.len())?;
        out.declare_action(action.clone());
    }
    for (clause, premises) in source.clauses().iter().zip(problem.premises()) {
        out.add_clause(clause_rewrite(
            clause, premises, layout, &mut used, control,
        )?);
    }
    if source.is_fixedpoint_format() {
        out.set_fixedpoint_format();
    }
    control.poll()?;
    out.validate().ok()?;
    control.poll()?;
    Some(out)
}

fn clause_rewrite(
    clause: &HornClause,
    premises: &[crate::quantified::UniversalPremise],
    layout: &Layout,
    used: &mut DetHashSet<String>,
    control: &SourceControl<'_>,
) -> Option<HornClause> {
    source_premises::preflight_clause(clause, control)?;
    let mut fresh = Vec::new();
    let head = match &clause.head {
        ClauseHead::False => ClauseHead::False,
        ClauseHead::Predicate(id, args) => {
            for (position, sort) in layout.axes(*id)?.iter().enumerate() {
                control.bytes(sort_bytes(sort)?)?;
                fresh.push(ChcExpr::var(ChcVar::new(
                    super::names::fresh(*id, position, used, control)?,
                    sort.clone(),
                )));
            }
            ClauseHead::Predicate(*id, layout.actuals(*id, args, &fresh, control)?)
        }
    };
    let mut predicates = Vec::new();
    for (id, args) in &clause.body.predicates {
        control.charge(args.len())?;
        // A fixedpoint error marker (or scalar-only successor) has no fresh
        // head axes either. Its source reads are equally valid search probes.
        let observed = if fresh.is_empty() {
            clause.body.constraint.as_ref().and_then(|constraint| {
                super::candidate::query_axes(constraint, args, *id, layout, control)
            })
        } else {
            None
        };
        control.poll()?;
        let axes = match observed {
            Some(axes) => axes,
            None => fallback_axes(*id, args, &clause.head, layout, &fresh, control)?,
        };
        predicates.push((*id, layout.actuals(*id, args, &axes, control)?));
    }
    let mut indices = fresh;
    let triggers = super::super::collect_index_terms(clause, super::super::INDEX_TERM_CAP);
    control.charge(triggers.len())?;
    indices.extend(triggers);
    let mut conjuncts = Vec::new();
    if let Some(constraint) = &clause.body.constraint {
        conjuncts.push(constraint.clone());
    }
    conjuncts.extend(source_premises::instances(premises, &indices, control)?);
    let constraint = ChcExpr::and_all_checked(conjuncts, || control.poll().is_none())?;
    source_premises::preflight(&constraint, control, &mut 0)?;
    let mut rewritten = HornClause::new(ClauseBody::new(predicates, Some(constraint)), head);
    rewritten.source_query_ordinal = clause.source_query_ordinal;
    control.poll()?;
    Some(rewritten)
}

fn fallback_axes(
    id: PredicateId,
    args: &[ChcExpr],
    source_head: &ClauseHead,
    layout: &Layout,
    head: &[ChcExpr],
    control: &SourceControl<'_>,
) -> Option<Vec<ChcExpr>> {
    let correspondence = transport::correspondence(id, args, source_head, layout, control)?;
    control.charge(head.len().checked_add(correspondence.len())?)?;
    let mut reserved = vec![false; head.len()];
    for position in correspondence.iter().flatten() {
        *reserved.get_mut(*position)? = true;
    }
    let mut out = Vec::new();
    out.try_reserve_exact(correspondence.len()).ok()?;
    for (position, sort) in layout.axes(id)?.iter().enumerate() {
        control.charge(1)?;
        let ChcSort::BitVec(width) = sort else {
            return None;
        };
        let transported = correspondence.get(position).copied().flatten();
        let selected = transported
            .or_else(|| (!reserved.get(position).copied().unwrap_or(true)).then_some(position));
        out.push(match selected.and_then(|index| head.get(index)) {
            Some(expr) if &expr.sort() == sort => {
                source_premises::preflight(expr, control, &mut 0)?;
                expr.clone()
            }
            _ => ChcExpr::BitVec(0, *width),
        });
    }
    control.poll()?;
    Some(out)
}
