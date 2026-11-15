// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn build(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    work: &mut WorkBudget<'_>,
) -> Result<storage::State, QueryError> {
    let reads = scan::reads(solver, values, work)?;
    let arrays = order(solver, values, &reads, work)?;
    let mut result = storage::empty(solver, work)?;
    let bound = owned::reserve_table::<TermId>(arrays.len(), work)?;
    result
        .model
        .read_conflicted
        .try_reserve(arrays.len())
        .map_err(|_| work.refuse_exhaustion())?;
    for &array in &arrays {
        work.charge(16)?;
        let Some((value, conflicted)) = entry(solver, values, &reads, array, work)? else {
            return Err(work.refuse_exhaustion());
        };
        storage::insert(&mut result, array, value, work)?;
        if conflicted {
            owned::table_insert(bound, work)?;
            result.model.read_conflicted.insert(array);
        }
    }
    let visits = owned::checked(reads.len().checked_add(arrays.len()), work)?;
    work.charge(visits)?;
    drop(reads);
    drop(arrays);
    work.charge(0)?;
    Ok(result)
}

fn order(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    reads: &[scan::Read<'_>],
    work: &mut WorkBudget<'_>,
) -> Result<Vec<TermId>, QueryError> {
    let mut result = owned::reserve_vec(solver.terms.len(), work)?;
    owned::scan_table::<(TermId, crate::ArrayVarData)>(solver.array_vars.allocation_size(), work)?;
    for &term in solver.array_vars.keys() {
        work.charge(16)?;
        let (rows, default) = originals(solver, values, term, work)?;
        let present = !rows.is_empty() || default.is_some();
        work.charge(rows.len() + 1)?;
        drop(rows);
        work.charge(0)?;
        if present {
            add(&mut result, term, work)?;
        }
    }
    owned::scan_table::<(TermId, TermId)>(solver.default_cache.allocation_size(), work)?;
    for (&array, &term) in &solver.default_cache {
        if scan::value(solver, values, term, work)?.is_some_and(|v| !v.is_empty()) {
            add(&mut result, array, work)?;
        }
    }
    for read in reads {
        work.charge(16)?;
        add(&mut result, read.array, work)?;
    }
    Ok(result)
}

fn add(
    values: &mut Vec<TermId>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let visits = owned::checked(
        values.len().checked_mul(16).and_then(|n| n.checked_add(16)),
        work,
    )?;
    work.charge(visits)?;
    if !values.contains(&term) {
        if values.len() >= values.capacity() {
            return Err(work.refuse_exhaustion());
        }
        values.push(term);
    }
    Ok(())
}
