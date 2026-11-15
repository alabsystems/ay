// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) struct Read<'a> {
    pub(super) array: TermId,
    pub(super) row: ModelCellRow<'a>,
}

pub(super) fn lookup<'a, T>(
    map: &'a HashMap<TermId, T>,
    key: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<Option<&'a T>, QueryError> {
    let buckets = table_bound(map, work)?;
    owned::table_insert(buckets, work)?;
    Ok(map.get(&key))
}

fn table_bound<T>(
    map: &HashMap<TermId, T>,
    work: &mut WorkBudget<'_>,
) -> Result<usize, QueryError> {
    if std::mem::size_of::<usize>() > 8 {
        return Err(work.refuse_exhaustion());
    }
    // Pinned raw layout: allocated size >= buckets * entry size. capacity()
    // is only items+growth_left and can decrease with tombstones. This is
    // backing metadata used to bound visits, NOT an RSS-to-work conversion.
    let entries = map.allocation_size() / std::mem::size_of::<(TermId, T)>();
    entries
        .checked_add(32)
        .ok_or_else(|| work.refuse_exhaustion())
}

fn table_scan<T>(map: &HashMap<TermId, T>, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    let visits = table_bound(map, work)?
        .checked_mul(8)
        .and_then(|n| n.checked_add(1))
        .ok_or_else(|| work.refuse_exhaustion())?;
    work.charge(visits)
}

pub(super) fn live(
    solver: &ArraySolver<'_>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(1)?;
    if term.0 as usize >= solver.terms.len() {
        return Err(work.refuse_exhaustion());
    }
    Ok(())
}

pub(super) fn value<'a>(
    solver: &ArraySolver<'_>,
    values: &'a HashMap<TermId, String>,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<Option<&'a str>, QueryError> {
    live(solver, term, work)?;
    Ok(lookup(values, term, work)?.map(String::as_str))
}

pub(super) fn chain(
    solver: &ArraySolver<'_>,
    array: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(usize, TermId), QueryError> {
    let mut current = array;
    for count in 0..=solver.store_cache.len() {
        live(solver, current, work)?;
        let Some(&(parent, _, _)) = lookup(&solver.store_cache, current, work)? else {
            return Ok((count, current));
        };
        current = parent;
    }
    Err(work.refuse_exhaustion())
}

fn equal(left: &str, right: &str, work: &mut WorkBudget<'_>) -> Result<bool, QueryError> {
    work.charge(1)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left
        .as_bytes()
        .chunks(128)
        .zip(right.as_bytes().chunks(128))
    {
        let visits = left
            .len()
            .checked_add(right.len())
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| work.refuse_exhaustion())?;
        work.charge(visits)?;
        if left != right {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn reads<'a>(
    solver: &ArraySolver<'_>,
    values: &'a HashMap<TermId, String>,
    work: &mut WorkBudget<'_>,
) -> Result<Vec<Read<'a>>, QueryError> {
    table_scan(&solver.select_cache, work)?;
    let mut reads = owned::reserve_vec(solver.select_cache.len(), work)?;
    for (&select, &(array, index)) in &solver.select_cache {
        let Some(index) = value(solver, values, index, work)?.filter(|v| !v.is_empty()) else {
            continue;
        };
        let Some(value) = value(solver, values, select, work)?.filter(|v| !v.is_empty()) else {
            continue;
        };
        if let Some(base) = read_base(solver, values, array, index, work)? {
            reads.push(Read {
                array: base,
                row: ModelCellRow {
                    key: ModelCellKey::Text(index),
                    value,
                },
            });
        }
    }
    work.charge(0)?;
    Ok(reads)
}

fn read_base(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    array: TermId,
    index: &str,
    work: &mut WorkBudget<'_>,
) -> Result<Option<TermId>, QueryError> {
    let mut base = array;
    for _ in 0..=solver.store_cache.len() {
        live(solver, base, work)?;
        let Some(&(parent, store_index, _)) = lookup(&solver.store_cache, base, work)? else {
            return Ok(Some(base));
        };
        let Some(stored) = value(solver, values, store_index, work)?.filter(|v| !v.is_empty())
        else {
            return Ok(None);
        };
        if equal(stored, index, work)? {
            return Ok(None);
        }
        base = parent;
    }
    Err(work.refuse_exhaustion())
}

pub(super) fn arrays(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    reads: &[Read<'_>],
    work: &mut WorkBudget<'_>,
) -> Result<Vec<TermId>, QueryError> {
    let maximum = solver
        .array_vars
        .len()
        .checked_add(solver.default_cache.len())
        .and_then(|n| n.checked_add(reads.len()))
        .ok_or_else(|| work.refuse_exhaustion())?;
    let mut arrays = owned::reserve_vec(maximum, work)?;
    table_scan(&solver.array_vars, work)?;
    for &array in solver.array_vars.keys() {
        insert(&mut arrays, array, work)?;
    }
    table_scan(&solver.default_cache, work)?;
    for (&array, &term) in &solver.default_cache {
        if value(solver, values, term, work)?.is_some_and(|v| !v.is_empty()) {
            insert(&mut arrays, array, work)?;
        }
    }
    for read in reads {
        insert(&mut arrays, read.array, work)?;
    }
    Ok(arrays)
}

fn insert(
    arrays: &mut Vec<TermId>,
    array: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let visits = arrays
        .len()
        .checked_add(1)
        .ok_or_else(|| work.refuse_exhaustion())?;
    work.charge(visits)?;
    if !arrays.contains(&array) {
        arrays.push(array);
    }
    Ok(())
}
