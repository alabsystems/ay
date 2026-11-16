// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod defaults;
pub(super) use defaults::shared;

pub(super) struct Chain<'a> {
    pub(super) store: TermId,
    pub(super) base: TermId,
    pub(super) writes: Vec<(&'a str, &'a str)>,
}

pub(super) struct DefaultSources<'a, 'values> {
    pub(super) members: &'a [TermId],
    pub(super) bases: &'a [TermId],
    pub(super) unwritten: &'a [(String, String)],
    pub(super) chains: &'a [Chain<'values>],
}

pub(super) fn capture<'a>(
    solver: &ArraySolver<'_>,
    values: &'a HashMap<TermId, String>,
    class: &[TermId],
    work: &mut WorkBudget<'_>,
) -> Result<Vec<Chain<'a>>, QueryError> {
    let mut result = owned::reserve_vec(class.len(), work)?;
    for &member in class {
        work.charge(32)?;
        let (count, base) = scan::chain(solver, member, work)?;
        let visits = owned::checked(
            class.len().checked_mul(16).and_then(|n| n.checked_add(16)),
            work,
        )?;
        work.charge(visits)?;
        if count == 0 || class.contains(&base) {
            continue;
        }
        let mut writes = owned::reserve_vec(count, work)?;
        let mut current = member;
        let mut complete = true;
        for _ in 0..count {
            work.charge(32)?;
            let &(parent, index, value) = scan::lookup(&solver.store_cache, current, work)?
                .ok_or_else(|| work.refuse_exhaustion())?;
            let index = scan::value(solver, values, index, work)?.filter(|v| !v.is_empty());
            let value = scan::value(solver, values, value, work)?.filter(|v| !v.is_empty());
            if let (Some(index), Some(value)) = (index, value) {
                writes.push((index, value));
            } else {
                complete = false;
                break;
            }
            current = parent;
        }
        if complete {
            result.push(Chain {
                store: member,
                base,
                writes,
            });
        } else {
            work.charge(writes.len() + 1)?;
            drop(writes);
        }
        work.charge(0)?;
    }
    Ok(result)
}

pub(super) fn bases(
    chains: &[Chain<'_>],
    work: &mut WorkBudget<'_>,
) -> Result<Vec<TermId>, QueryError> {
    let mut result = owned::reserve_vec(chains.len(), work)?;
    for chain in chains {
        work.charge(32)?;
        result.push(chain.base);
    }
    // Paid insertion sort: identical ascending TermId order to the legacy
    // unstable sort, with equal IDs subsequently removed, no opaque sorter.
    for index in 1..result.len() {
        work.charge(32)?;
        let value = result[index];
        let mut position = index;
        while position > 0 {
            work.charge(32)?;
            if result[position - 1].0 <= value.0 {
                break;
            }
            result[position] = result[position - 1];
            position -= 1;
        }
        work.charge(16)?;
        result[position] = value;
    }
    let visits = owned::checked(result.len().checked_mul(16), work)?;
    work.charge(visits)?;
    result.dedup();
    Ok(result)
}

pub(super) fn members(
    solver: &ArraySolver<'_>,
    class: &[TermId],
    work: &mut WorkBudget<'_>,
) -> Result<Vec<TermId>, QueryError> {
    let mut result = owned::reserve_vec(class.len(), work)?;
    for &member in class {
        if scan::lookup(&solver.store_cache, member, work)?.is_none()
            && scan::lookup(&solver.array_vars, member, work)?.is_some()
        {
            work.charge(16)?;
            result.push(member);
        }
    }
    Ok(result)
}

pub(super) fn unwritten(
    model: &ArrayModel,
    chains: &[Chain<'_>],
    members: &[TermId],
    bases: &[TermId],
    work: &mut WorkBudget<'_>,
) -> Result<Vec<(String, String)>, QueryError> {
    let mut result = Vec::new();
    work.admit(32, 8 * size_of::<Vec<(String, String)>>())?;
    for &term in members.iter().chain(bases) {
        let Some(value) = scan::lookup(&model.array_values, term, work)? else {
            continue;
        };
        for (index, value) in &value.stores {
            work.charge(16)?;
            let mut written = false;
            for chain in chains {
                for &(key, _) in &chain.writes {
                    if storage::equal(key, index, work)? {
                        written = true;
                        break;
                    }
                }
                if written {
                    break;
                }
            }
            if !written {
                let row = (owned::text(index, work)?, owned::text(value, work)?);
                storage::push(&mut result, row, work)?;
            }
        }
    }
    Ok(result)
}
