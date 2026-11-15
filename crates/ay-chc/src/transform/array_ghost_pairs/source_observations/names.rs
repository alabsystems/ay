// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::records::Registry;
use crate::PredicateId;
use ay_core::kani_compat::DetHashSet;

pub(super) fn reserved(
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    control: &SourceControl<'_>,
) -> Option<DetHashSet<String>> {
    let mut out = DetHashSet::default();
    for name in crate::quantified::functions::controlled::names(problem, control)? {
        out.insert(name.to_owned());
    }
    for name in registry.term_names().chain(
        problem
            .source_problem()
            .predicates()
            .iter()
            .map(|p| p.name.as_str()),
    ) {
        control.bytes(name.len())?;
        out.insert(name.to_owned());
    }
    for (clause, premises) in problem
        .source_problem()
        .clauses()
        .iter()
        .zip(problem.premises())
    {
        source_premises::preflight_clause(clause, control)?;
        for premise in premises {
            source_premises::preflight(premise.matrix(), control, &mut 0)?;
        }
        for var in source_premises::clause_variables(clause, premises, control)? {
            control.bytes(var.name.len())?;
            out.insert(var.name);
        }
        source_premises::reserve_names(premises, &mut out, control)?;
    }
    Some(out)
}

pub(super) fn fresh(
    predicate: PredicateId,
    position: usize,
    used: &mut DetHashSet<String>,
    control: &SourceControl<'_>,
) -> Option<String> {
    let mut name = format!("ay!observation!{}!{position}", predicate.index());
    loop {
        control.bytes(name.len())?;
        if used.insert(name.clone()) {
            return Some(name);
        }
        name.push('_');
    }
}
