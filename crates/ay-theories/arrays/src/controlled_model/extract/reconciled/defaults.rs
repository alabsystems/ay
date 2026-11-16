// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod parents;

pub(super) fn fill(
    plan: &classes::Plan,
    solver: &ArraySolver<'_>,
    model: &mut ArrayModel,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let rounds = owned::checked(model.array_values.len().checked_add(1), work)?;
    for _ in 0..rounds {
        work.charge(32)?;
        let mut changed = classes(plan, model, work)?;
        changed |= forward(solver, model, work)?;
        changed |= parents::apply(solver, model, work)?;
        if !changed {
            break;
        }
    }
    work.charge(0)
}

fn classes(
    plan: &classes::Plan,
    model: &mut ArrayModel,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    let mut changed = false;
    let mut begin = 0;
    for &end in &plan.ends {
        work.charge(16)?;
        let class = plan
            .members
            .get(begin..end)
            .ok_or_else(|| work.refuse_exhaustion())?;
        let mut default: Option<String> = None;
        let mut conflict = false;
        for &term in class {
            let value =
                scan::lookup(&model.array_values, term, work)?.and_then(|v| v.default.as_deref());
            if let Some(value) = value {
                if let Some(prior) = &default {
                    if !storage::equal(prior, value, work)? {
                        conflict = true;
                        break;
                    }
                } else {
                    default = Some(owned::text(value, work)?);
                }
            }
        }
        if !conflict {
            if let Some(value) = &default {
                for &term in class {
                    changed |= assign(model, term, value, work)?;
                }
            }
        }
        work.charge(16)?;
        drop(default);
        work.charge(0)?;
        begin = end;
    }
    Ok(changed)
}

fn forward(
    solver: &ArraySolver<'_>,
    model: &mut ArrayModel,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    owned::scan_table::<(TermId, ArrayInterpretation)>(model.array_values.allocation_size(), work)?;
    let mut pending = owned::reserve_vec(model.array_values.len(), work)?;
    // Like legacy, ALL pending term/base pairs precede any forward assignment.
    for (&term, value) in &model.array_values {
        work.charge(16)?;
        if value.default.is_none() {
            let (_, base) = scan::chain(solver, term, work)?;
            pending.push((term, base));
        }
    }
    let mut changed = false;
    for &(term, base) in &pending {
        work.charge(16)?;
        if base == term {
            continue;
        }
        let value =
            scan::lookup(&model.array_values, base, work)?.and_then(|v| v.default.as_deref());
        if let Some(value) = value {
            let value = owned::text(value, work)?;
            changed |= assign(model, term, &value, work)?;
            work.charge(16)?;
            drop(value);
        }
    }
    work.charge(pending.len() + 1)?;
    drop(pending);
    work.charge(0)?;
    Ok(changed)
}

fn assign(
    model: &mut ArrayModel,
    term: TermId,
    value: &str,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    if scan::lookup(&model.array_values, term, work)?.is_none_or(|v| v.default.is_some()) {
        return Ok(false);
    }
    let value = owned::text(value, work)?;
    let bound = owned::checked(
        model
            .array_values
            .allocation_size()
            .checked_div(size_of::<(TermId, ArrayInterpretation)>())
            .and_then(|n| n.checked_add(32)),
        work,
    )?;
    owned::table_insert(bound, work)?;
    let target = model
        .array_values
        .get_mut(&term)
        .ok_or_else(|| work.refuse_exhaustion())?;
    work.charge(16)?;
    target.default = Some(value);
    Ok(true)
}
