// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Project only argument positions certified by the MUST-constant analysis.

use ay_core::kani_compat::DetHashMap;

use crate::{ChcExpr, ChcProblem, ClauseBody, ClauseHead, PredicateId};

use super::{ground, rewrite_budget};

pub(super) fn project(
    original: &ChcProblem,
    constants: &DetHashMap<PredicateId, Vec<(usize, ChcExpr)>>,
    budget: &mut ground::Budget,
) -> Result<(ChcProblem, Vec<Vec<usize>>), ground::Stopped> {
    let mut kept = Vec::new();
    for predicate in original.predicates() {
        budget.charge(predicate.arity() + 1)?;
        let mut constant = vec![false; predicate.arity()];
        if let Some(values) = constants.get(&predicate.id) {
            for (position, _) in values {
                budget.charge(1)?;
                *constant.get_mut(*position).ok_or_else(|| budget.stop())? = true;
            }
        }
        kept.push(
            (0..predicate.arity())
                .filter(|position| !constant[*position])
                .collect::<Vec<_>>(),
        );
    }
    budget.charge(0)?;
    let mut projected = original.clone();
    projected
        .project_predicate_signatures(&kept, &mut || budget.charge(1).is_ok())
        .ok_or_else(|| budget.stop())?;
    for clause in projected.clauses_mut() {
        let substitutions = rewrite_budget::substitutions(clause, constants, budget)?;
        rewrite_budget::reserve(clause, &substitutions, budget)?;
        let mut conjuncts: Vec<_> = clause
            .body
            .constraint
            .as_ref()
            .map(|constraint| {
                constraint
                    .substitute(&substitutions)
                    .simplify_array_ops()
                    .simplify_constants()
            })
            .into_iter()
            .collect();
        let occurrences = clause
            .body
            .predicates
            .iter()
            .map(|(predicate, arguments)| (predicate, arguments))
            .chain(
                match &clause.head {
                    ClauseHead::Predicate(predicate, arguments) => Some((predicate, arguments)),
                    ClauseHead::False => None,
                }
                .into_iter(),
            );
        for (predicate, arguments) in occurrences {
            budget.charge(arguments.len() + 1)?;
            if let Some(values) = constants.get(predicate) {
                for (position, value) in values {
                    let argument = arguments.get(*position).ok_or_else(|| budget.stop())?;
                    rewrite_budget::reserve_matching_guard(argument, value, budget)?;
                    // Keep EVERY match, including literals, expressions and
                    // repeated variables pinned to different constants. A
                    // variable substitution alone would silently erase a
                    // contradictory second premise after projection.
                    conjuncts.push(ChcExpr::eq(
                        argument.substitute(&substitutions),
                        value.clone(),
                    ));
                }
            }
        }
        let predicates = clause
            .body
            .predicates
            .iter()
            .map(|(predicate, arguments)| {
                let positions = kept.get(predicate.0 as usize)?;
                let arguments = positions
                    .iter()
                    .map(|position| {
                        arguments
                            .get(*position)
                            .map(|arg| arg.substitute(&substitutions))
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some((*predicate, arguments))
            })
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| budget.stop())?;
        clause.body = ClauseBody::new(
            predicates,
            Some(ChcExpr::and_all(conjuncts).simplify_constants()),
        );
        if let ClauseHead::Predicate(predicate, arguments) = &mut clause.head {
            *arguments = kept
                .get(predicate.0 as usize)
                .ok_or_else(|| budget.stop())?
                .iter()
                .map(|position| {
                    arguments
                        .get(*position)
                        .map(|arg| arg.substitute(&substitutions))
                })
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| budget.stop())?;
        }
    }
    // Retain even false clauses: indices, actions and source-query ordinals
    // stay exact. Reachability may prune them in its own recorded transform.
    budget.charge(0)?;
    Ok((projected, kept))
}
