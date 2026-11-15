// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Canonical complete-source identity plus exact mapped raw clause identity.
//! This is not equality of every unused raw AST, nor an aggregate trace lift.

use super::*;

pub(super) fn retain_source(source: &str, control: &Control<'_>) -> ChcResult<Arc<str>> {
    let bytes = source
        .len()
        .checked_add(64)
        .ok_or_else(|| invalid("aggregate source allocation"))?;
    control.charge(0, bytes)?;
    let source = Arc::from(source);
    control.poll()?;
    Ok(source)
}

pub(super) fn authenticate(
    obligation: &QuantifiedChcQueryObligation,
    aggregate: &QuantifiedChcProblem,
    control: &Control<'_>,
) -> ChcResult<()> {
    if authenticate_inner(obligation, aggregate, control).is_err() {
        return control.refuse("aggregate association refused");
    }
    // All temporary plans, definition indices and census/cone scratch have
    // been destroyed before this final shared-budget publication checkpoint.
    control.poll()
}

fn authenticate_inner(
    obligation: &QuantifiedChcQueryObligation,
    aggregate: &QuantifiedChcProblem,
    control: &Control<'_>,
) -> ChcResult<()> {
    identity(obligation, aggregate, control)?;
    let plan = matching_plan(aggregate, &obligation.id, control)?;
    let census = copy::Census::new(aggregate, control)?;
    let selected = plan::cone(aggregate, &plan, &census.definitions, control)?;
    // This prepays structural equality at known source positions. No slice
    // copy charge, clause clone, source parse or whole-batch reslicing occurs.
    census.charge_conservation(&selected, plan.selected(), control)?;
    origins::validate(
        aggregate,
        &plan,
        &selected,
        &obligation.problem,
        &obligation.id.clause_origins,
        control,
    )
}

fn identity(
    obligation: &QuantifiedChcQueryObligation,
    aggregate: &QuantifiedChcProblem,
    control: &Control<'_>,
) -> ChcResult<()> {
    let id = &obligation.id;
    let original = aggregate.source_smtlib();
    let slice = obligation.problem.source_smtlib();
    let bytes = original
        .len()
        .checked_add(id.aggregate_source.len())
        .and_then(|bytes| bytes.checked_add(slice.len()))
        .and_then(|bytes| bytes.checked_add(id.aggregate_source_sha256.len()))
        .and_then(|bytes| bytes.checked_add(id.content_sha256.len()))
        .and_then(|bytes| bytes.checked_add(128))
        .ok_or_else(|| invalid("association source identity allowance"))?;
    control.charge(2, bytes)?;
    if original != id.aggregate_source.as_ref()
        || digest(original) != id.aggregate_source_sha256
        || digest(slice) != id.content_sha256
    {
        return control.refuse("association source identity mismatch");
    }
    control.poll()
}

fn matching_plan(
    aggregate: &QuantifiedChcProblem,
    id: &QuantifiedChcQueryId,
    control: &Control<'_>,
) -> ChcResult<plan::Plan> {
    let plans = plan::plans(aggregate, control)?;
    let mut matching = None;
    for plan in plans {
        control.charge(1, 0)?;
        if plan.ordinal == id.source_query_ordinal
            && plan.query == id.query_clause_index
            && plan.definition == id.defining_clause_index
        {
            control.charge(0, id.label.len())?;
            if matching.is_some() || plan.label != id.label {
                return control.refuse("association query label or uniqueness");
            }
            matching = Some(plan);
        }
    }
    matching.ok_or_else(|| invalid("association query plan mismatch"))
}

#[cfg(test)]
mod tests;
