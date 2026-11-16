// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn apply(
    plan: &classes::Plan,
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    state: &mut storage::State,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let mut begin = 0;
    for &end in &plan.ends {
        work.charge(16)?;
        let class = plan
            .members
            .get(begin..end)
            .ok_or_else(|| work.refuse_exhaustion())?;
        one(solver, values, class, state, work)?;
        begin = end;
    }
    work.charge(0)
}

fn one(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    class: &[TermId],
    state: &mut storage::State,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let chains = chains::capture(solver, values, class, work)?;
    if chains.is_empty() {
        drop(chains);
        return work.charge(0);
    }
    let bases = chains::bases(&chains, work)?;
    let members = chains::members(solver, class, work)?;
    let unwritten = chains::unwritten(&state.model, &chains, &members, &bases, work)?;
    let (default, conflict) = chains::shared(
        solver,
        values,
        &state.model,
        chains::DefaultSources {
            members: &members,
            bases: &bases,
            unwritten: &unwritten,
            chains: &chains,
        },
        work,
    )?;
    for &base in &bases {
        if scan::lookup(&solver.const_array_cache, base, work)?.is_some() {
            continue;
        }
        let value = storage::interpretation(solver, state, base, work)?;
        fill(value, &unwritten, default.as_deref(), conflict, work)?;
    }
    for chain in &chains {
        let value = storage::interpretation(solver, state, chain.store, work)?;
        fill(value, &unwritten, default.as_deref(), conflict, work)?;
    }
    for &member in &members {
        let value = storage::interpretation(solver, state, member, work)?;
        for chain in &chains {
            for &(index, text) in &chain.writes {
                storage::missing_row(value, index, text, work)?;
            }
        }
        fill(value, &unwritten, default.as_deref(), conflict, work)?;
    }
    let visits = owned::checked(
        chains
            .len()
            .checked_add(bases.len())
            .and_then(|n| n.checked_add(members.len()))
            .and_then(|n| n.checked_add(unwritten.len()))
            .and_then(|n| n.checked_add(1)),
        work,
    )?;
    work.charge(visits)?;
    drop(chains);
    drop(bases);
    drop(members);
    drop(unwritten);
    drop(default);
    work.charge(0)
}

fn fill(
    target: &mut ArrayInterpretation,
    rows: &[(String, String)],
    default: Option<&str>,
    conflict: bool,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    for (index, value) in rows {
        storage::missing_row(target, index, value, work)?;
    }
    work.charge(16)?;
    if target.default.is_none() && !conflict {
        target.default = owned::optional_text(default, work)?;
    }
    Ok(())
}
