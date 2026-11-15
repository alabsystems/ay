// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::mem::{align_of, size_of};

pub(super) fn checked(
    value: Option<usize>,
    work: &mut WorkBudget<'_>,
) -> Result<usize, QueryError> {
    value.ok_or_else(|| work.refuse_exhaustion())
}

pub(super) fn reserve_vec<T>(
    count: usize,
    work: &mut WorkBudget<'_>,
) -> Result<Vec<T>, QueryError> {
    let bytes = checked(
        count
            .checked_mul(size_of::<T>())
            .and_then(|n| n.checked_mul(8))
            .and_then(|n| n.checked_add(4 * size_of::<Vec<T>>())),
        work,
    )?;
    let visits = checked(count.checked_mul(8).and_then(|n| n.checked_add(1)), work)?;
    work.admit(visits, bytes)?;
    let mut result = Vec::new();
    result
        .try_reserve_exact(count)
        .map_err(|_| work.refuse_exhaustion())?;
    work.charge(0)?;
    Ok(result)
}

pub(super) fn text(source: &str, work: &mut WorkBudget<'_>) -> Result<String, QueryError> {
    let bytes = checked(
        source
            .len()
            .checked_mul(8)
            .and_then(|n| n.checked_add(8 * size_of::<String>())),
        work,
    )?;
    let visits = checked(
        source.len().checked_mul(3).and_then(|n| n.checked_add(4)),
        work,
    )?;
    work.admit(visits, bytes)?;
    let mut result = String::new();
    result
        .try_reserve_exact(source.len())
        .map_err(|_| work.refuse_exhaustion())?;
    // All generated model values/names in this cohort are <=130 ASCII bytes.
    work.charge(source.len())?;
    result.push_str(source);
    work.charge(0)?;
    Ok(result)
}

pub(super) fn scan_table<T>(
    allocation: usize,
    work: &mut WorkBudget<'_>,
) -> Result<usize, QueryError> {
    if size_of::<usize>() > 8 {
        return Err(work.refuse_exhaustion());
    }
    let count = checked(
        allocation
            .checked_div(size_of::<T>())
            .and_then(|n| n.checked_add(32)),
        work,
    )?;
    let visits = checked(count.checked_mul(8).and_then(|n| n.checked_add(1)), work)?;
    work.charge(visits)?;
    Ok(count)
}

pub(super) fn reserve_table<T>(
    count: usize,
    work: &mut WorkBudget<'_>,
) -> Result<usize, QueryError> {
    if size_of::<usize>() > 8 {
        return Err(work.refuse_exhaustion());
    }
    let buckets = checked(count.checked_mul(4).and_then(|n| n.checked_add(32)), work)?;
    let bytes = checked(
        size_of::<T>()
            .checked_add(1)
            .and_then(|n| n.checked_mul(buckets))
            .and_then(|n| n.checked_add(align_of::<T>().max(16)))
            .and_then(|n| n.checked_add(16))
            .and_then(|n| n.checked_mul(4)),
        work,
    )?;
    let visits = checked(buckets.checked_mul(16).and_then(|n| n.checked_add(1)), work)?;
    work.admit(visits, bytes)?;
    Ok(buckets)
}

pub(super) fn probe(buckets: usize, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    let visits = checked(
        buckets.checked_mul(8).and_then(|n| n.checked_add(512)),
        work,
    )?;
    work.charge(visits)
}

pub(super) fn name_probe(buckets: usize, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    // Keys are const-array/default/select/store, <=11 bytes. Cover fixed
    // hash and BOTH compared payloads in every possible bucket, not only slots.
    let visits = checked(
        buckets.checked_mul(32).and_then(|n| n.checked_add(512)),
        work,
    )?;
    work.charge(visits)
}

pub(super) fn lookup<'a, T>(
    table: &'a HashMap<TermId, T>,
    key: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<Option<&'a T>, QueryError> {
    work.charge(64)?;
    let bound = scan_table::<(TermId, T)>(table.allocation_size(), work)?;
    probe(bound, work)?;
    Ok(table.get(&key))
}

pub(super) fn finish<T>(
    result: Result<T, QueryError>,
    work: &mut WorkBudget<'_>,
) -> Result<T, QueryError> {
    match result {
        Err(error) => {
            let _ = work.charge(0);
            Err(error)
        }
        Ok(value) => match work.charge(0) {
            Ok(()) => Ok(value),
            Err(error) => {
                drop(value);
                let _ = work.charge(0);
                Err(error)
            }
        },
    }
}
