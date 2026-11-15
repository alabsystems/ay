// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-record replay, distinct from the generic ghost certificate route.

use super::*;
use crate::quantified::functions::controlled;
use crate::quantified::records::Registry;
use crate::quantified::UniversalPremise;
use crate::ClauseBody;

#[cfg(test)]
mod tests;

pub(super) fn registry(
    problem: &QuantifiedChcProblem,
    projection: Option<&RecordProjection>,
    control: &SourceControl<'_>,
) -> Option<Option<Registry>> {
    match projection {
        None if !problem.source_problem().uses_datatype_features() => {
            if problem.function_declarations().is_empty() {
                return Some(None);
            }
            // An empty record registry still authenticates scalar/array sorts.
            // This explicit-source renderer must not infer UF declarations.
            control.bytes(crate::quantified::records::registry_bytes(
                problem.source_problem(),
            )?)?;
            Some(Some(Registry::new(problem.source_problem()).ok()?))
        }
        Some(projection) if projection.matches_source(problem, control) => {
            // Charge registry construction, declaration formatting and a later
            // finite-context registry clone before any of them allocates.
            let bytes = crate::quantified::records::registry_bytes(problem.source_problem())?;
            control.bytes(bytes.checked_mul(3)?)?;
            let registry = Registry::new(problem.source_problem()).ok()?;
            control.poll()?;
            Some(Some(registry))
        }
        _ => None,
    }
}

pub(super) fn project_clause(
    original: &HornClause,
    projection: &RecordProjection,
    control: &SourceControl<'_>,
) -> Option<HornClause> {
    source_premises::preflight_clause(original, control)?;
    let mut predicates = Vec::new();
    control.charge(original.body.predicates.len())?;
    for (predicate, args) in &original.body.predicates {
        predicates.push((
            *predicate,
            projection.project_arguments(*predicate, args, control)?,
        ));
    }
    let head = match &original.head {
        ClauseHead::False => ClauseHead::False,
        ClauseHead::Predicate(predicate, args) => ClauseHead::Predicate(
            *predicate,
            projection.project_arguments(*predicate, args, control)?,
        ),
    };
    // Only predicate actuals are projected, through ORIGINAL record selectors.
    // The constraint and universal matrices remain in the original DT theory.
    let mut clause = HornClause::new(
        ClauseBody::new(predicates, original.body.constraint.clone()),
        head,
    );
    clause.source_query_ordinal = original.source_query_ordinal;
    control.poll()?;
    Some(clause)
}

/// The candidate was checked over projected signatures. All functions below
/// originate from authenticated source records, their selector projections or
/// the complete retained ordinary-function registry. No declaration is inferred
/// from a finite hint or model, and no function interpretation is fixed here.
pub(super) fn render(
    problem: &QuantifiedChcProblem,
    registry: &Registry,
    interpretation: &GhostPairModel,
    clause: &HornClause,
    variables: &[ChcVar],
    fresh_vars: &[ChcVar],
    head_negation: Option<&ChcExpr>,
    used: &mut FxHashSet<String>,
    hints: &[ChcExpr],
    premises: &[UniversalPremise],
    control: &SourceControl<'_>,
) -> Option<String> {
    let bodies = quantified_body_instances(interpretation, clause, used)?;
    let mut bytes = 1024usize;
    for expression in clause
        .body
        .constraint
        .iter()
        .chain(head_negation)
        .chain(hints)
        .chain(premises.iter().map(UniversalPremise::matrix))
        .chain(bodies.iter().map(|(_, body)| body))
    {
        source_premises::preflight(expression, control, &mut bytes)?;
        if !problem.function_declarations().is_empty()
            && controlled::expression_sort(problem, registry, expression, control)? != ChcSort::Bool
        {
            return None;
        }
    }
    for var in variables
        .iter()
        .chain(fresh_vars)
        .chain(premises.iter().flat_map(UniversalPremise::binders))
        .chain(bodies.iter().flat_map(|(vars, _)| vars))
    {
        registry.validate_sort(&var.sort).ok()?;
        let cost = var
            .name
            .len()
            .checked_mul(4)?
            .checked_add(crate::quantified::records::sort_bytes(&var.sort)?)?;
        bytes = bytes.checked_add(cost)?;
        control.bytes(cost)?;
    }
    let header = registry.declarations_smtlib().ok()?;
    let functions = controlled::declarations_smtlib(problem, control)?;
    bytes = bytes
        .checked_add(header.len())?
        .checked_add(functions.len())?;
    if bytes > MAX_REPLAY_BYTES {
        return None;
    }
    control.bytes(bytes)?;
    control.poll()?;
    let mut smt = String::from("(set-logic ALL)\n");
    smt.push_str(&header);
    smt.push_str(&functions);
    for var in variables.iter().chain(fresh_vars) {
        smt.push_str(&format!(
            "(declare-const {} {})\n",
            quote_symbol(&var.name),
            sort_to_smtlib(&var.sort)
        ));
    }
    if let Some(constraint) = &clause.body.constraint {
        assertion(&mut smt, constraint);
    }
    for premise in premises {
        let binders = source_premises::binder_list(premise, Some(control))?;
        smt.push_str(&format!(
            "(assert (forall ({binders}) {}))\n",
            InvariantModel::expr_to_smtlib(premise.matrix())
        ));
    }
    emit_quantified_body_instances(&mut smt, &bodies);
    for hint in hints {
        assertion(&mut smt, hint);
    }
    if let Some(negation) = head_negation {
        assertion(&mut smt, negation);
    }
    smt.push_str("(check-sat)\n");
    control.poll()?;
    (smt.len() <= MAX_REPLAY_BYTES).then_some(smt)
}

fn assertion(output: &mut String, expr: &ChcExpr) {
    output.push_str(&format!(
        "(assert {})\n",
        InvariantModel::expr_to_smtlib(expr)
    ));
}
