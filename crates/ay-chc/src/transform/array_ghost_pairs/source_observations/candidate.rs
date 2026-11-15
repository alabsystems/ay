// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

mod expression;

use super::super::candidate_flow::{
    bounded_reverse_transports, CandidateControl, CandidateTransport, MAX_PROPAGATED_CANDIDATES,
};
use super::super::candidate_model::CandidateAtom;
use super::super::candidate_usage::{query_argument_positions, scalar_candidate_node_count};
use super::*;
use crate::{ChcExpr, ChcProblem, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

pub(super) fn pools(
    problem: &QuantifiedChcProblem,
    raw: &ChcProblem,
    layout: &Layout,
    control: &SourceControl<'_>,
) -> Option<DetHashMap<PredicateId, Vec<CandidateAtom>>> {
    let source = problem.source_problem();
    let source_control = Some(CandidateControl {
        cancellation: control.cancellation,
        deadline: control.deadline,
    });
    let slice = super::super::candidate_query::bounded_query_slice(source, source_control)?;
    let mut pools = DetHashMap::default();
    let mut count = 0usize;
    for query in slice.anchors {
        control.poll()?;
        source_premises::preflight_clause(query, control)?;
        let [(predicate, args)] = query.body.predicates.as_slice() else {
            continue;
        };
        let Some(constraint) = &query.body.constraint else {
            continue;
        };
        let positions = query_argument_positions(args, layout.original_sorts(*predicate)?)?;
        let identity: Vec<_> = (0..args.len()).map(Some).collect();
        let Some(formula) = expression::rewrite(
            constraint, &positions, *predicate, &identity, layout, control,
        ) else {
            control.poll()?;
            continue;
        };
        let required = required_arguments(*predicate, &formula, layout, control)?;
        let mut transports =
            bounded_reverse_transports(source, *predicate, &required, source_control)?;
        // Same-position typed proposals also cover store-updated CFG columns.
        // These are untrusted guesses, checked by whole-system Houdini/replay.
        for target in source.predicates() {
            control.poll()?;
            if target
                .arg_sorts
                .starts_with(layout.original_sorts(*predicate)?)
                && !transports
                    .iter()
                    .any(|t| t.predicate == target.id && t.source_to_target == identity)
            {
                if transports.len() >= MAX_PROPAGATED_CANDIDATES {
                    return None;
                }
                transports.push(CandidateTransport {
                    predicate: target.id,
                    source_to_target: identity.clone(),
                });
            }
        }
        for transport in transports {
            let formula =
                if transport.predicate == *predicate && transport.source_to_target == identity {
                    Some(formula.clone())
                } else {
                    expression::rewrite(
                        constraint,
                        &positions,
                        transport.predicate,
                        &transport.source_to_target,
                        layout,
                        control,
                    )
                };
            let Some(formula) = formula else {
                control.poll()?;
                continue;
            };
            insert(
                raw,
                layout,
                transport.predicate,
                formula,
                &mut pools,
                &mut count,
                control,
            )?;
        }
    }
    for predicate in slice.sink_predicates {
        if !layout.canonical(predicate)?.is_empty() {
            return None;
        }
        insert(
            raw,
            layout,
            predicate,
            ChcExpr::Bool(false),
            &mut pools,
            &mut count,
            control,
        )?;
    }
    control.poll()?;
    Some(pools)
}

fn insert(
    raw: &ChcProblem,
    layout: &Layout,
    predicate: PredicateId,
    formula: ChcExpr,
    pools: &mut DetHashMap<PredicateId, Vec<CandidateAtom>>,
    count: &mut usize,
    control: &SourceControl<'_>,
) -> Option<()> {
    source_premises::preflight(&formula, control, &mut 0)?;
    super::budget::scalar_validation(raw, control)?;
    for var in layout.canonical(predicate)? {
        control.charge(1)?;
        control.bytes(
            var.name
                .len()
                .checked_add(crate::quantified::records::sort_bytes(&var.sort)?)?,
        )?;
    }
    scalar_candidate_node_count(raw, layout.canonical(predicate)?, &formula)?;
    let pool = pools.entry(predicate).or_default();
    if !pool.iter().any(|candidate| candidate.formula == formula) {
        *count = count.checked_add(1)?;
        if *count > MAX_PROPAGATED_CANDIDATES {
            return None;
        }
        pool.push(CandidateAtom { formula });
    }
    control.poll()
}

fn required_arguments(
    id: PredicateId,
    formula: &ChcExpr,
    layout: &Layout,
    control: &SourceControl<'_>,
) -> Option<DetHashSet<usize>> {
    source_premises::preflight(formula, control, &mut 0)?;
    let used = super::super::certify::certificate_formula_vars(formula)?;
    let predicate = layout.predicate(id)?;
    let mut required = DetHashSet::default();
    for (position, var) in predicate.canonical.iter().enumerate() {
        control.charge(1)?;
        if !used.contains(var) {
            continue;
        }
        let argument = if position < predicate.original.len() {
            position
        } else {
            let offset = position.checked_sub(predicate.original.len())?;
            if offset < predicate.axes.len() {
                predicate
                    .observations
                    .iter()
                    .find(|obs| obs.path.contains(&layout::Step::Axis(offset)))?
                    .argument
            } else {
                predicate
                    .observations
                    .get(offset.checked_sub(predicate.axes.len())?)?
                    .argument
            }
        };
        required.insert(argument);
    }
    Some(required)
}

/// Preserve the query's actually observed row/column tuple in the raw body.
pub(super) fn query_axes(
    constraint: &ChcExpr,
    args: &[ChcExpr],
    id: PredicateId,
    layout: &Layout,
    control: &SourceControl<'_>,
) -> Option<Vec<ChcExpr>> {
    let predicate = layout.predicate(id)?;
    let positions = query_argument_positions(args, &predicate.original)?;
    let accesses = super::access::collect(constraint, &positions, layout, control)?;
    let mut terms = vec![None; predicate.axes.len()];
    for access in accesses {
        let (_, observation) = super::access::matching(predicate, &access, access.argument)?;
        for (step, actual) in observation.path.iter().zip(&access.path) {
            if let (layout::Step::Axis(axis), super::access::AccessStep::Index(expr)) =
                (step, actual)
            {
                source_premises::preflight(expr, control, &mut 0)?;
                match terms.get_mut(*axis)? {
                    Some(prior) if &*prior != *expr => return None,
                    Some(_) => {}
                    slot @ None => *slot = Some((**expr).clone()),
                }
            }
        }
    }
    terms
        .into_iter()
        .zip(&predicate.axes)
        .map(|(term, sort)| {
            let ChcSort::BitVec(width) = sort else {
                return None;
            };
            Some(term.unwrap_or(ChcExpr::BitVec(0, *width)))
        })
        .collect()
}
